const params = new URLSearchParams(window.location.search);
let ROOM = params.get('room');
if (ROOM) {
    try { localStorage.setItem('playsla.room', ROOM); } catch (_) {}
} else {
    try { ROOM = localStorage.getItem('playsla.room'); } catch (_) {}
}
if (!ROOM) ROOM = 'default';

const SIGNALING_URL =
    'wss://playsla-signaling.faytonserver.workers.dev/ws?role=tesla&room='
    + encodeURIComponent(ROOM);

const $ = (id) => document.getElementById(id);
const video = $('screen');
const overlay = $('overlay');

function setStatus(el, text, kind = '') {
    el.textContent = text;
    el.className = 'value' + (kind ? ' ' + kind : '');
}
const stat = {
    sig:     (t, k) => setStatus($('s-sig'),     t, k),
    peer:    (t, k) => setStatus($('s-peer'),    t, k),
    decoder: (t, k) => setStatus($('s-decoder'), t, k),
    stream:  (t, k) => setStatus($('s-stream'),  t, k),
};

const state = {
    ws: null,
    pc: null,
    nalChan: null,
    touchChan: null,
    remoteSet: false,
    pendingCandidates: [],

    mediaSource: null,
    sourceBuffer: null,
    mediaSourceInitInFlight: false,
    appendQueue: [],
    muxer: null,
    waitingForKey: true,
    framesIn: 0,
    bytesIn: 0,
    lastResyncMs: 0,
};

const RTC_CONFIG = {
    iceServers: [
        { urls: 'stun:stun.l.google.com:19302' },
        { urls: 'stun:stun1.l.google.com:19302' },
    ],
};

function splitAnnexB(u) {
    const nals = [];
    const starts = [];
    let i = 0;
    while (i < u.length - 2) {
        const sc4 = (i + 3 < u.length &&
                     u[i] === 0 && u[i+1] === 0 && u[i+2] === 0 && u[i+3] === 1) ? 4 : 0;
        const sc3 = (!sc4 && u[i] === 0 && u[i+1] === 0 && u[i+2] === 1) ? 3 : 0;
        const sc = sc4 || sc3;
        if (sc > 0) { starts.push({ off: i, sc }); i += sc; }
        else i++;
    }
    for (let k = 0; k < starts.length; k++) {
        const s = starts[k];
        const begin = s.off + s.sc;
        const end = (k + 1 < starts.length) ? starts[k + 1].off : u.length;
        if (end > begin) nals.push(u.subarray(begin, end));
    }
    return nals;
}

function avcCtoAnnexB(u) {
    if (u.length < 7 || u[0] !== 0x01) return null;
    let p = 5;
    const out = [];
    const SC = [0, 0, 0, 1];
    const numSps = u[p++] & 0x1f;
    for (let i = 0; i < numSps; i++) {
        if (p + 2 > u.length) return null;
        const len = (u[p] << 8) | u[p+1]; p += 2;
        if (len <= 0 || p + len > u.length) return null;
        out.push(...SC);
        for (let j = 0; j < len; j++) out.push(u[p + j]);
        p += len;
    }
    if (p >= u.length) return null;
    const numPps = u[p++];
    for (let i = 0; i < numPps; i++) {
        if (p + 2 > u.length) return null;
        const len = (u[p] << 8) | u[p+1]; p += 2;
        if (len <= 0 || p + len > u.length) return null;
        out.push(...SC);
        for (let j = 0; j < len; j++) out.push(u[p + j]);
        p += len;
    }
    return new Uint8Array(out);
}

class BitReader {
    constructor(u8) { this.u = u8; this.bytePos = 0; this.bitPos = 0; }
    readBit() {
        const b = (this.u[this.bytePos] >> (7 - this.bitPos)) & 1;
        if (++this.bitPos === 8) { this.bitPos = 0; this.bytePos++; }
        return b;
    }
    readBits(n) {
        let v = 0;
        for (let i = 0; i < n; i++) v = (v << 1) | this.readBit();
        return v;
    }

    readUe() {
        let zeros = 0;
        while (this.bytePos < this.u.length && this.readBit() === 0) zeros++;
        const v = this.readBits(zeros);
        return (1 << zeros) - 1 + v;
    }
    readSe() {
        const ue = this.readUe();
        return ue & 1 ? (ue + 1) >> 1 : -(ue >> 1);
    }
}

function rbspUnescape(u) {
    const out = [];
    for (let i = 0; i < u.length; i++) {
        if (i + 2 < u.length && u[i] === 0 && u[i+1] === 0 && u[i+2] === 0x03) {
            out.push(0, 0); i += 2;
        } else {
            out.push(u[i]);
        }
    }
    return new Uint8Array(out);
}

function parseSps(sps) {
    if (sps.length < 4 || (sps[0] & 0x1f) !== 7) return null;



    const body = rbspUnescape(sps.subarray(1));
    if (body.length < 4) return null;
    const profile_idc = body[0];
    const constraint  = body[1];
    const level_idc   = body[2];
    const br = new BitReader(body.subarray(3));
    try {
        br.readUe();
        const HIGH_PROFILES = [100, 110, 122, 244, 44, 83, 86, 118, 128, 138, 139, 134, 135];
        if (HIGH_PROFILES.includes(profile_idc)) {
            const chroma_format_idc = br.readUe();
            if (chroma_format_idc === 3) br.readBit();
            br.readUe();
            br.readUe();
            br.readBit();
            const seq_scaling_matrix_present = br.readBit();
            if (seq_scaling_matrix_present) {
                const count = (chroma_format_idc !== 3) ? 8 : 12;
                for (let i = 0; i < count; i++) {
                    if (br.readBit()) {
                        const sz = (i < 6) ? 16 : 64;
                        let lastScale = 8, nextScale = 8;
                        for (let j = 0; j < sz; j++) {
                            if (nextScale !== 0) {
                                const delta = br.readSe();
                                nextScale = (lastScale + delta + 256) & 0xff;
                            }
                            lastScale = (nextScale === 0) ? lastScale : nextScale;
                        }
                    }
                }
            }
        }
        br.readUe();
        const pic_order_cnt_type = br.readUe();
        if (pic_order_cnt_type === 0) {
            br.readUe();
        } else if (pic_order_cnt_type === 1) {
            br.readBit();
            br.readSe();
            br.readSe();
            const n = br.readUe();
            for (let i = 0; i < n; i++) br.readSe();
        }
        br.readUe();
        br.readBit();
        const pic_width_in_mbs_minus1 = br.readUe();
        const pic_height_in_map_units_minus1 = br.readUe();
        const frame_mbs_only_flag = br.readBit();
        if (!frame_mbs_only_flag) br.readBit();
        br.readBit();
        const frame_cropping_flag = br.readBit();
        let crop_left = 0, crop_right = 0, crop_top = 0, crop_bottom = 0;
        if (frame_cropping_flag) {
            crop_left   = br.readUe();
            crop_right  = br.readUe();
            crop_top    = br.readUe();
            crop_bottom = br.readUe();
        }
        const width  = (pic_width_in_mbs_minus1 + 1) * 16 - 2 * (crop_left + crop_right);
        const height = (2 - frame_mbs_only_flag) * (pic_height_in_map_units_minus1 + 1) * 16
                       - (2 - frame_mbs_only_flag) * (crop_top + crop_bottom);
        return { profile_idc, constraint, level_idc, width, height };
    } catch (e) {
        return null;
    }
}

function fourCC(s) { return [s.charCodeAt(0), s.charCodeAt(1), s.charCodeAt(2), s.charCodeAt(3)]; }
function u16(n) { return [(n >>> 8) & 0xff, n & 0xff]; }
function u32(n) { return [(n >>> 24) & 0xff, (n >>> 16) & 0xff, (n >>> 8) & 0xff, n & 0xff]; }
function u64(n) {

    const hi = Math.floor(n / 0x100000000);
    const lo = n >>> 0;
    return [...u32(hi), ...u32(lo)];
}

function box(type, ...payloadParts) {
    let totalPayload = 0;
    for (const p of payloadParts) totalPayload += p.length;
    const size = 8 + totalPayload;
    const out = new Uint8Array(size);
    let p = 0;
    out.set(u32(size), p); p += 4;
    out.set(fourCC(type), p); p += 4;
    for (const part of payloadParts) {
        out.set(part, p); p += part.length;
    }
    return out;
}

function fullBox(type, version, flags, ...payloadParts) {
    const prefix = new Uint8Array([version, (flags >>> 16) & 0xff, (flags >>> 8) & 0xff, flags & 0xff]);
    return box(type, prefix, ...payloadParts);
}
function concat(...arrs) {
    let total = 0;
    for (const a of arrs) total += a.length;
    const out = new Uint8Array(total);
    let p = 0;
    for (const a of arrs) { out.set(a, p); p += a.length; }
    return out;
}

class Mp4Muxer {
    constructor() {
        this.sps = null;
        this.pps = null;
        this.spsInfo = null;
        this.timescale = 90000;
        this.fps = 30;
        this.sequenceNumber = 1;
        this.baseDecodeTime = 0;
        this.trackId = 1;
        this.initEmitted = false;
        this.codecString = 'avc1.42E01F';
    }

    get sampleDuration() { return Math.round(this.timescale / this.fps); }

    feed(annexB) {
        const nals = splitAnnexB(annexB);
        const slices = [];

        for (const nal of nals) {
            const type = nal[0] & 0x1f;
            if (type === 7) {

                if (!this.sps || !bytesEq(this.sps, nal)) {
                    this.sps = new Uint8Array(nal);
                    this.spsInfo = parseSps(nal);
                    if (this.spsInfo) {
                        const hex = (n) => n.toString(16).padStart(2, '0').toUpperCase();
                        this.codecString = `avc1.${hex(this.spsInfo.profile_idc)}${hex(this.spsInfo.constraint)}${hex(this.spsInfo.level_idc)}`;
                    }
                }
            } else if (type === 8) {
                if (!this.pps || !bytesEq(this.pps, nal)) {
                    this.pps = new Uint8Array(nal);
                }
            } else if (type === 5 || type === 1) {
                slices.push(nal);
            }

        }

        let init = null;
        if (!this.initEmitted && this.sps && this.pps && this.spsInfo) {
            init = this.buildInit();
            this.initEmitted = true;
        }

        let fragment = null;
        let isKey = false;
        if (slices.length > 0 && this.initEmitted) {
            isKey = slices.some(n => (n[0] & 0x1f) === 5);
            fragment = this.buildFragment(slices, isKey);
            this.sequenceNumber++;
            this.baseDecodeTime += this.sampleDuration;
        }
        return { init, fragment, isKey };
    }

    buildInit() {
        const ftyp = box('ftyp',
            new Uint8Array(fourCC('isom')),
            new Uint8Array(u32(0x00000200)),
            new Uint8Array(fourCC('isom')),
            new Uint8Array(fourCC('iso2')),
            new Uint8Array(fourCC('avc1')),
            new Uint8Array(fourCC('mp41')),
        );

        const moov = box('moov',
            this.buildMvhd(),
            this.buildTrak(),
            this.buildMvex(),
        );

        return concat(ftyp, moov);
    }

    buildMvhd() {


        return fullBox('mvhd', 0, 0,
            new Uint8Array(u32(0)),
            new Uint8Array(u32(0)),
            new Uint8Array(u32(this.timescale)),
            new Uint8Array(u32(0)),
            new Uint8Array(u32(0x00010000)),
            new Uint8Array(u16(0x0100)),
            new Uint8Array(u16(0)),
            new Uint8Array(u32(0)), new Uint8Array(u32(0)),
            new Uint8Array([
                0,1,0,0,  0,0,0,0,  0,0,0,0,
                0,0,0,0,  0,1,0,0,  0,0,0,0,
                0,0,0,0,  0,0,0,0,  0x40,0,0,0,
            ]),
            new Uint8Array(24),
            new Uint8Array(u32(this.trackId + 1)),
        );
    }

    buildTrak() {
        return box('trak',
            this.buildTkhd(),
            this.buildMdia(),
        );
    }

    buildTkhd() {
        const w = this.spsInfo.width;
        const h = this.spsInfo.height;
        return fullBox('tkhd', 0, 0x000007,
            new Uint8Array(u32(0)),
            new Uint8Array(u32(0)),
            new Uint8Array(u32(this.trackId)),
            new Uint8Array(u32(0)),
            new Uint8Array(u32(0)),
            new Uint8Array(u32(0)), new Uint8Array(u32(0)),
            new Uint8Array(u16(0)),
            new Uint8Array(u16(0)),
            new Uint8Array(u16(0)),
            new Uint8Array(u16(0)),
            new Uint8Array([
                0,1,0,0,  0,0,0,0,  0,0,0,0,
                0,0,0,0,  0,1,0,0,  0,0,0,0,
                0,0,0,0,  0,0,0,0,  0x40,0,0,0,
            ]),
            new Uint8Array(u32(w << 16)),
            new Uint8Array(u32(h << 16)),
        );
    }

    buildMdia() {
        return box('mdia',
            fullBox('mdhd', 0, 0,
                new Uint8Array(u32(0)),
                new Uint8Array(u32(0)),
                new Uint8Array(u32(this.timescale)),
                new Uint8Array(u32(0)),
                new Uint8Array([0x55, 0xc4]),
                new Uint8Array(u16(0)),
            ),
            fullBox('hdlr', 0, 0,
                new Uint8Array(u32(0)),
                new Uint8Array(fourCC('vide')),
                new Uint8Array(u32(0)), new Uint8Array(u32(0)), new Uint8Array(u32(0)),
                new Uint8Array([...'VideoHandler'].map(c => c.charCodeAt(0)).concat([0])),
            ),
            this.buildMinf(),
        );
    }

    buildMinf() {
        return box('minf',
            fullBox('vmhd', 0, 1,
                new Uint8Array(u16(0)),
                new Uint8Array(u16(0)), new Uint8Array(u16(0)), new Uint8Array(u16(0)),
            ),
            box('dinf',
                fullBox('dref', 0, 0,
                    new Uint8Array(u32(1)),
                    fullBox('url ', 0, 1),
                ),
            ),
            this.buildStbl(),
        );
    }

    buildStbl() {
        return box('stbl',
            this.buildStsd(),
            fullBox('stts', 0, 0, new Uint8Array(u32(0))),
            fullBox('stsc', 0, 0, new Uint8Array(u32(0))),
            fullBox('stsz', 0, 0, new Uint8Array(u32(0)), new Uint8Array(u32(0))),
            fullBox('stco', 0, 0, new Uint8Array(u32(0))),
        );
    }

    buildStsd() {

        const w = this.spsInfo.width;
        const h = this.spsInfo.height;

        const avcC = this.buildAvcC();

        const compressorName = new Uint8Array(32);

        const avc1 = box('avc1',
            new Uint8Array(6),
            new Uint8Array(u16(1)),
            new Uint8Array(u16(0)),
            new Uint8Array(u16(0)),
            new Uint8Array(u32(0)), new Uint8Array(u32(0)), new Uint8Array(u32(0)),
            new Uint8Array(u16(w)),
            new Uint8Array(u16(h)),
            new Uint8Array(u32(0x00480000)),
            new Uint8Array(u32(0x00480000)),
            new Uint8Array(u32(0)),
            new Uint8Array(u16(1)),
            compressorName,
            new Uint8Array(u16(0x0018)),
            new Uint8Array(u16(0xffff)),
            avcC,
        );

        return fullBox('stsd', 0, 0,
            new Uint8Array(u32(1)),
            avc1,
        );
    }

    buildAvcC() {
        const sps = this.sps;
        const pps = this.pps;



        const parts = [
            new Uint8Array([
                0x01,
                this.spsInfo.profile_idc,
                this.spsInfo.constraint,
                this.spsInfo.level_idc,
                0xff,
                0xe1,
            ]),
            new Uint8Array(u16(sps.length)),
            sps,
            new Uint8Array([0x01]),
            new Uint8Array(u16(pps.length)),
            pps,
        ];
        return box('avcC', ...parts);
    }

    buildMvex() {
        return box('mvex',
            fullBox('trex', 0, 0,
                new Uint8Array(u32(this.trackId)),
                new Uint8Array(u32(1)),
                new Uint8Array(u32(this.sampleDuration)),
                new Uint8Array(u32(0)),
                new Uint8Array(u32(0x00010000)),
            ),
        );
    }

    buildFragment(slices, isKey) {

        let mdatPayloadLen = 0;
        for (const s of slices) mdatPayloadLen += 4 + s.length;
        const mdatPayload = new Uint8Array(mdatPayloadLen);
        let p = 0;
        for (const s of slices) {
            mdatPayload.set(u32(s.length), p); p += 4;
            mdatPayload.set(s, p); p += s.length;
        }
        const mdat = box('mdat', mdatPayload);





        const trunFlags = 0x000201 | (isKey ? 0x000004 : 0x000000);

        const sampleSize = mdatPayloadLen;
        const sampleCount = 1;



        const firstSampleFlags = isKey ? 0x02000000 : 0x00010000;


        const trun = fullBox('trun', 0, trunFlags,
            new Uint8Array(u32(sampleCount)),
            new Uint8Array(u32(0)),
            ...(isKey ? [new Uint8Array(u32(firstSampleFlags))] : []),
            new Uint8Array(u32(sampleSize)),
        );


        const tfhd = fullBox('tfhd', 0, 0x020008,
            new Uint8Array(u32(this.trackId)),
            new Uint8Array(u32(this.sampleDuration)),
        );

        const tfdt = fullBox('tfdt', 1, 0,
            new Uint8Array(u64(this.baseDecodeTime)),
        );

        const traf = box('traf', tfhd, tfdt, trun);

        const mfhd = fullBox('mfhd', 0, 0,
            new Uint8Array(u32(this.sequenceNumber)),
        );


        let moof = box('moof', mfhd, traf);






        const trunOffsetInMoof = moof.length - trun.length;
        const dataOffsetField = trunOffsetInMoof + 12 + 4;
        const dataOffset = moof.length + 8;

        const view = new DataView(moof.buffer, moof.byteOffset, moof.byteLength);
        view.setUint32(dataOffsetField, dataOffset);

        return concat(moof, mdat);
    }
}

function bytesEq(a, b) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
    return true;
}

function setupMediaSource(codecString) {
    if (!('MediaSource' in window)) {
        stat.decoder('нет MediaSource', 'err');
        return Promise.reject(new Error('no MediaSource'));
    }
    const mimeType = `video/mp4; codecs="${codecString}"`;
    if (!MediaSource.isTypeSupported(mimeType)) {
        stat.decoder('не поддержан: ' + codecString, 'err');
        return Promise.reject(new Error('unsupported codec: ' + codecString));
    }
    return new Promise((resolve, reject) => {
        const ms = new MediaSource();
        state.mediaSource = ms;
        video.src = URL.createObjectURL(ms);
        ms.addEventListener('sourceopen', () => {
            try {
                const sb = ms.addSourceBuffer(mimeType);


                sb.mode = 'sequence';
                sb.addEventListener('updateend', drainQueue);
                sb.addEventListener('error', (e) => {
                    console.error('[SourceBuffer.error]', e);
                });
                state.sourceBuffer = sb;
                stat.decoder('готов (' + codecString + ')', 'ok');
                resolve(sb);
            } catch (e) {
                stat.decoder('addSourceBuffer failed: ' + e.message, 'err');
                reject(e);
            }
        }, { once: true });
        ms.addEventListener('sourceended', () => console.warn('[MediaSource] ended'));
        ms.addEventListener('sourceclose', () => console.warn('[MediaSource] closed'));
    });
}

function appendToBuffer(bytes) {
    state.appendQueue.push(bytes);
    drainQueue();
}

function drainQueue() {
    const sb = state.sourceBuffer;
    if (!sb || sb.updating) return;
    if (state.appendQueue.length === 0) {

        pruneBuffer();
        return;
    }
    const next = state.appendQueue.shift();
    try { sb.appendBuffer(next); }
    catch (e) {

        if (e.name === 'QuotaExceededError') {
            state.appendQueue.unshift(next);
            try {
                const buffered = sb.buffered;
                if (buffered.length > 0) {
                    const end = buffered.end(buffered.length - 1);
                    const start = buffered.start(0);
                    if (end - start > 1) {
                        sb.remove(start, end - 0.5);
                    }
                }
            } catch (_) {}
        } else {
            console.warn('appendBuffer failed', e);
        }
    }
}

function pruneBuffer() {
    const sb = state.sourceBuffer;
    if (!sb || sb.updating || !video) return;
    const buffered = sb.buffered;
    if (buffered.length === 0) return;
    const now = video.currentTime;
    const start = buffered.start(0);

    const keepBackTo = now - 0.3;
    if (start < keepBackTo) {
        try { sb.remove(start, keepBackTo); } catch (_) {}
    }
}

function maybeSnapToLive() {
    const sb = state.sourceBuffer;
    if (!sb || !video || video.paused) return;
    const buffered = sb.buffered;
    if (buffered.length === 0) return;
    const liveEdge = buffered.end(buffered.length - 1);
    const drift = liveEdge - video.currentTime;
    state.lastDrift = drift;
    if (drift > 0.25) {
        const now = performance.now();
        if (now - state.lastResyncMs > 200) {
            state.lastResyncMs = now;
            try {
                video.currentTime = Math.max(0, liveEdge - 0.02);
                video.playbackRate = 1.0;
                state.snapCount = (state.snapCount || 0) + 1;
            } catch (_) {}
        }
    } else if (drift > 0.08) {
        if (video.playbackRate < 1.28) {
            try { video.playbackRate = 1.3; } catch (_) {}
        }
    } else if (drift < 0.04 && video.playbackRate !== 1.0) {
        try { video.playbackRate = 1.0; } catch (_) {}
    }
}

function onBinary(buf) {
    let u = new Uint8Array(buf);
    state.framesIn++;
    state.bytesIn += u.byteLength;



    if (u.length > 7 && u[0] === 0x01) {
        const annexB = avcCtoAnnexB(u);
        if (annexB) u = annexB;
    }

    if (!state.muxer) state.muxer = new Mp4Muxer();
    const { init, fragment, isKey } = state.muxer.feed(u);




    if (init && !state.sourceBuffer && !state.mediaSourceInitInFlight) {
        state.mediaSourceInitInFlight = true;
        setupMediaSource(state.muxer.codecString)
            .then(() => { state.mediaSourceInitInFlight = false; drainQueue(); })
            .catch(() => { state.mediaSourceInitInFlight = false; });
    }
    if (init) appendToBuffer(init);



    if (init && state.sourceBuffer && !state.mediaSourceInitInFlight) {

    }

    if (!fragment) return;



    if (state.waitingForKey) {
        if (!isKey) return;
        state.waitingForKey = false;
    }

    appendToBuffer(fragment);

    if (state.muxer.spsInfo) {
        stat.stream(`${state.muxer.spsInfo.width}×${state.muxer.spsInfo.height}`, 'ok');
        overlay.classList.add('hidden');
    }

    maybeSnapToLive();
}

function onText(text) {
    let msg; try { msg = JSON.parse(text); } catch { return; }

    if (msg.type === 'sdp-answer') {
        const sdp = msg.sdp;
        if (sdp && state.pc) {
            state.pc.setRemoteDescription(new RTCSessionDescription({
                type: sdp.type, sdp: sdp.sdp,
            })).then(() => {
                state.remoteSet = true;
                const queued = state.pendingCandidates;
                state.pendingCandidates = [];
                for (const c of queued) {
                    state.pc.addIceCandidate(new RTCIceCandidate(c))
                        .catch(err => console.warn('queued addIceCandidate failed', err));
                }
            }).catch(err => {
                console.warn('setRemoteDescription failed', err);
                stat.peer('SDP: ' + (err?.message || err), 'err');
            });
        }
        return;
    }
    if (msg.type === 'ice-candidate' && msg.candidate && state.pc) {
        if (!state.remoteSet) {
            state.pendingCandidates.push(msg.candidate);
            return;
        }
        state.pc.addIceCandidate(new RTCIceCandidate(msg.candidate))
            .catch(err => console.warn('addIceCandidate failed', err));
        return;
    }
    const restart = () => { closePeer(); stat.decoder('—'); stat.stream('—'); };

    if (msg.type === 'room-state') {
        const phonePresent = msg.peers && msg.peers.includes('phone');
        stat.peer(phonePresent ? 'найден' : 'ожидание', phonePresent ? 'ok' : '');
        if (phonePresent) { restart(); startOffer(); }
        return;
    }
    if (msg.type === 'peer-joined' && msg.role === 'phone') {
        stat.peer('найден', 'ok');
        restart();
        startOffer();
        return;
    }
    if (msg.type === 'peer-left' && msg.role === 'phone') {
        stat.peer('отключился', 'err');
        closePeer();
        stat.decoder('—');
        stat.stream('—');
        return;
    }
    if (msg.t === 'hello') {
        stat.peer('найден', 'ok');
        return;
    }
}

function bindTouch() {
    const send = (phase, x, y, id) => {
        const payload = JSON.stringify({
            t: 'touch', p: phase, id: id ?? 0,
            x: Math.max(0, Math.min(1, x)),
            y: Math.max(0, Math.min(1, y)),
        });
        const ch = state.touchChan;
        if (ch && ch.readyState === 'open') { try { ch.send(payload); } catch (_) {} }
    };
    const pendingMoves = new Map();
    let rafScheduled = false;
    const flushMoves = () => {
        rafScheduled = false;
        if (pendingMoves.size === 0) return;
        for (const [id, p] of pendingMoves) send('move', p.x, p.y, id);
        pendingMoves.clear();
    };
    const queueMove = (id, x, y) => {
        pendingMoves.set(id, { x, y });
        if (!rafScheduled) {
            rafScheduled = true;
            requestAnimationFrame(flushMoves);
        }
    };
    const dropPendingMove = (id) => { pendingMoves.delete(id); };



    const xy = (e) => {
        const r = video.getBoundingClientRect();
        return [
            Math.max(0, Math.min(1, (e.clientX - r.left) / r.width)),
            Math.max(0, Math.min(1, (e.clientY - r.top)  / r.height)),
        ];
    };

    const DRAG_THRESHOLD = 0.01;
    const tracked = new Map();

    video.addEventListener('pointerdown', (e) => {
        try { video.setPointerCapture(e.pointerId); } catch {}
        const [x, y] = xy(e);
        tracked.set(e.pointerId, { downX: x, downY: y, dragging: false });
        send('down', x, y, e.pointerId);
    });
    video.addEventListener('pointermove', (e) => {
        if (e.buttons === 0 && e.pointerType !== 'touch') return;
        const t = tracked.get(e.pointerId);
        if (!t) return;
        const [x, y] = xy(e);
        if (!t.dragging) {
            const dx = x - t.downX, dy = y - t.downY;
            if (dx * dx + dy * dy < DRAG_THRESHOLD * DRAG_THRESHOLD) return;
            t.dragging = true;
        }
        queueMove(e.pointerId, x, y);
    });
    const up = (e) => {
        const t = tracked.get(e.pointerId);
        tracked.delete(e.pointerId);
        dropPendingMove(e.pointerId);
        const [x, y] = xy(e);
        if (t && !t.dragging) {
            send('up', t.downX, t.downY, e.pointerId);
        } else {
            send('up', x, y, e.pointerId);
        }
    };
    video.addEventListener('pointerup', up);
    video.addEventListener('pointercancel', up);
    video.addEventListener('touchstart', (e) => e.preventDefault(), { passive: false });


    video.addEventListener('contextmenu', (e) => e.preventDefault());
    video.addEventListener('dblclick', (e) => e.preventDefault());
}

async function ensurePeer() {
    if (state.pc) return state.pc;
    const pc = new RTCPeerConnection(RTC_CONFIG);
    state.pc = pc;

    const nalChan = pc.createDataChannel('nal', {
        ordered: true,
        priority: 'low',
    });
    nalChan.binaryType = 'arraybuffer';
    nalChan.onopen = () => stat.stream('канал готов', 'ok');
    nalChan.onmessage = (e) => {
        if (typeof e.data === 'string') return;
        onBinary(e.data);
    };
    nalChan.onclose = () => stat.stream('канал закрыт', 'err');
    state.nalChan = nalChan;

    const touchChan = pc.createDataChannel('touch', {
        ordered: true,
        priority: 'high',
    });
    touchChan.onopen  = () => {};
    touchChan.onclose = () => {};
    state.touchChan = touchChan;

    pc.oniceconnectionstatechange = () => {
        const s = pc.iceConnectionState;
        if (s === 'connected' || s === 'completed') stat.peer('подключён', 'ok');
        else if (s === 'failed' || s === 'disconnected' || s === 'closed') stat.peer('—');
    };
    pc.onicecandidate = (e) => {
        if (!e.candidate) return;
        if (!state.ws || state.ws.readyState !== WebSocket.OPEN) return;
        state.ws.send(JSON.stringify({
            type: 'ice-candidate',
            candidate: {
                sdpMid: e.candidate.sdpMid,
                sdpMLineIndex: e.candidate.sdpMLineIndex,
                candidate: e.candidate.candidate,
            },
        }));
    };

    return pc;
}

async function startOffer() {
    const pc = await ensurePeer();
    const offer = await pc.createOffer();
    await pc.setLocalDescription(offer);
    if (state.ws && state.ws.readyState === WebSocket.OPEN) {
        state.ws.send(JSON.stringify({
            type: 'sdp-offer',
            sdp: { type: pc.localDescription.type, sdp: pc.localDescription.sdp },
        }));
    }
}

function closePeer() {
    try { state.nalChan && state.nalChan.close(); } catch (_) {}
    try { state.touchChan && state.touchChan.close(); } catch (_) {}
    try { state.pc && state.pc.close(); } catch (_) {}
    state.nalChan = null; state.touchChan = null; state.pc = null;
    state.remoteSet = false;
    state.pendingCandidates = [];


    if (state.sourceBuffer) {
        try { state.mediaSource && state.mediaSource.endOfStream(); } catch (_) {}
    }
    state.sourceBuffer = null;
    state.mediaSource = null;
    state.mediaSourceInitInFlight = false;
    state.appendQueue = [];
    state.muxer = null;
    state.waitingForKey = true;
    try { video.removeAttribute('src'); video.load(); } catch (_) {}

    overlay.classList.remove('hidden');
}

function connect() {
    stat.sig('подключение…');
    const ws = new WebSocket(SIGNALING_URL);
    ws.binaryType = 'arraybuffer';
    state.ws = ws;

    ws.onopen = () => {
        stat.sig('подключено', 'ok');
    };
    ws.onerror = () => stat.sig('ошибка', 'err');
    ws.onclose = (e) => {
        stat.sig(`закрыт (${e.code})`, 'err');
        stat.peer('—'); stat.decoder('—'); stat.stream('—');
        closePeer();
        setTimeout(connect, 500);
    };
    ws.onmessage = (e) => {
        if (typeof e.data !== 'string') return;
        onText(e.data);
    };
}

bindTouch();
connect();
