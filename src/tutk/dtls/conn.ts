/**
 * DTLSConn — Full DTLS-based P2P connection to Wyze cameras.
 * Ported from go2rtc/pkg/tutk/dtls/conn_dtls.go
 *
 * Handles:
 * - UDP socket management
 * - Discovery (IOTC + CC51 protocols)
 * - DTLS handshake (via pion-style PSK)
 * - Message routing (keepalive, data, DTLS frames)
 * - Frame reassembly via FrameHandler
 */

import * as dgram from "node:dgram";
import { createHmac } from "node:crypto";
import { EventEmitter } from "node:events";
import { transCodeBlob, reverseTransCodeBlob } from "../crypto.js";
import { genSessionId } from "../helpers.js";
import { FrameHandler, type Packet, ChannelIVideo, ChannelAudio, ChannelPVideo } from "../frame.js";
import { derivePSK, calculateAuthKey } from "./auth.js";

// ─── Protocol constants ────────────────────────────────────────

const MAGIC_CC51 = "\x51\xcc";
const SDK_VERSION_42 = Buffer.from([0x01, 0x01, 0x02, 0x04]); // 4.2.1.1
const SDK_VERSION_43 = Buffer.from([0x00, 0x08, 0x03, 0x04]); // 4.3.8.0

// IOTC commands
const CMD_DISCO_REQ     = 0x0601;
const CMD_DISCO_RES     = 0x0602;
const CMD_SESSION_REQ   = 0x0402;
const CMD_SESSION_RES   = 0x0404;
const CMD_DATA_TX       = 0x0407;
const CMD_DATA_RX       = 0x0408;
const CMD_KEEPALIVE_REQ = 0x0427;
const CMD_KEEPALIVE_RES = 0x0428;

// CC51 commands
const CMD_DISCO_CC51     = 0x1002;
const CMD_KEEPALIVE_CC51 = 0x1202;
const CMD_DTLS_CC51      = 0x1502;
const PAYLOAD_SIZE_CC51  = 0x0028;
const PACKET_SIZE_CC51   = 52;
const HEADER_SIZE_CC51   = 28;
const AUTH_SIZE_CC51      = 20;
const KEEPALIVE_SIZE_CC51 = 48;

const HEADER_SIZE = 16;
const DISCO_BODY_SIZE = 72;
const SESSION_BODY = 36;

// Magic values for AV protocol
const MAGIC_AV_LOGIN_RESP  = 0x2100;
const MAGIC_IOCTRL         = 0x7000;
const MAGIC_CHANNEL_MSG    = 0x1000;
const MAGIC_ACK            = 0x0009;
const MAGIC_AV_LOGIN1      = 0x0000;
const MAGIC_AV_LOGIN2      = 0x2000;

const PROTO_VERSION  = 0x000c;
const DEFAULT_CAPS   = 0x001f07fb;

const IOTC_CHANNEL_MAIN = 0;
const IOTC_CHANNEL_BACK = 1;

// ─── DTLSConn ───────────────────────────────────────────────────

export interface DTLSConnOptions {
  host: string;
  port?: number;
  uid: string;
  authKey: string;
  enr: string;
  verbose?: boolean;
}

export class DTLSConn extends EventEmitter {
  private conn: dgram.Socket | null = null;
  private addr: { ip: string; port: number };
  private frames: FrameHandler;
  private verbose: boolean;
  private closed = false;

  // Identity
  private uid: string;
  private authKey: string;
  private enr: string;
  private psk: Buffer;

  // Session
  private sid: Buffer;
  private ticket = 0;
  private hasTwoWayStreaming_ = false;

  // Protocol
  private isCC51_ = false;
  private seq = 0;
  private seqCmd = 0;
  private avSeq = 0;
  private kaSeq = 0;

  // Ack tracking
  private ackFlags = 0;
  private rxSeqStart = 0xffff;
  private rxSeqEnd = 0xffff;
  private rxSeqInit = false;

  // Channels
  private clientBuf: Buffer[] = [];
  private serverBuf: Buffer[] = [];
  private rawCmdBuf: Buffer[] = [];
  private cmdWaiters: Array<(data: Buffer) => void> = [];
  private clientWaiters: Array<(data: Buffer) => void> = [];

  // DTLS connections (simplified - just buffers for now)
  private dtlsClientConn: any = null;

  constructor(opts: DTLSConnOptions) {
    super();
    this.addr = { ip: opts.host, port: opts.port ?? 32761 };
    this.uid = opts.uid;
    this.authKey = opts.authKey;
    this.enr = opts.enr;
    this.psk = derivePSK(opts.enr);
    this.verbose = opts.verbose ?? false;
    this.sid = genSessionId();
    this.frames = new FrameHandler(this.verbose);
  }

  get isCC51(): boolean { return this.isCC51_; }
  get hasTwoWayStreaming(): boolean { return this.hasTwoWayStreaming_; }

  // ─── Discovery ────────────────────────────────────────────────

  /**
   * Perform discovery: send IOTC and CC51 probes, wait for camera response.
   */
  async discovery(): Promise<void> {
    this.conn = dgram.createSocket("udp4");
    
    await new Promise<void>((resolve, reject) => {
      this.conn!.bind(0, () => resolve());
      setTimeout(() => reject(new Error("UDP bind timeout")), 5000);
    });

    if (this.verbose) {
      const la = this.conn.address();
      console.log(`[DTLS] Bound to ${la.address}:${la.port}`);
    }

    const pktIOTC = transCodeBlob(this.msgDisco(1));
    const pktCC51 = this.msgDiscoCC51(0, 0, false);

    const deadline = Date.now() + 5000;
    
    return new Promise<void>((resolve, reject) => {
      const check = () => {
        if (Date.now() > deadline) {
          cleanup();
          reject(new Error("Discovery timeout"));
          return;
        }

        // Send both probes
        this.conn!.send(pktIOTC, this.addr.port, this.addr.ip);
        this.conn!.send(pktCC51, this.addr.port, this.addr.ip);
      };

      const interval = setInterval(check, 100);

      const cleanup = () => {
        clearInterval(interval);
        this.conn!.removeAllListeners("message");
      };

      this.conn!.on("message", (msg, rinfo) => {
        if (rinfo.address !== this.addr.ip) return;

        // Check CC51
        if (msg.length >= PACKET_SIZE_CC51 && msg.subarray(0, 2).toString("binary") === MAGIC_CC51) {
          const cmd = msg.readUInt16LE(4);
          if (cmd === CMD_DISCO_CC51) {
            this.addr.port = rinfo.port;
            this.isCC51_ = true;
            this.ticket = msg.readUInt16LE(14);
            if (msg.length >= 24) {
              msg.copy(this.sid, 0, 16, 24);
            }
            cleanup();
            if (this.verbose) console.log(`[DTLS] Discovery: CC51 protocol, ticket=${this.ticket}`);
            this.discoDoneCC51().then(resolve).catch(reject);
            return;
          }
        }

        // Check IOTC
        const data = reverseTransCodeBlob(msg);
        if (data.length >= 16 && data.readUInt16LE(8) === CMD_DISCO_RES) {
          this.addr.port = rinfo.port;
          this.isCC51_ = false;
          cleanup();
          if (this.verbose) console.log(`[DTLS] Discovery: IOTC protocol`);
          this.discoDoneIOTC().then(resolve).catch(reject);
          return;
        }
      });

      // Start probing immediately
      check();
    });
  }

  private async discoDoneIOTC(): Promise<void> {
    // Send stage 2 (direct)
    await this.write(this.msgDisco(2));
    await new Promise(r => setTimeout(r, 100));
    
    // Send session request and wait for session response
    await this.writeAndWait(
      this.msgSession(),
      (res) => res.length >= 16 && res.readUInt16LE(8) === CMD_SESSION_RES
    );
  }

  private async discoDoneCC51(): Promise<void> {
    await this.writeAndWait(
      this.msgDiscoCC51(2, this.ticket, false),
      (res) => {
        if (res.length < PACKET_SIZE_CC51 || res.subarray(0, 2).toString("binary") !== MAGIC_CC51) return false;
        const cmd = res.readUInt16LE(4);
        const dir = res.readUInt16LE(8);
        const seq = res.readUInt16LE(12);
        return cmd === CMD_DISCO_CC51 && dir === 0xffff && seq === 3;
      }
    );
  }

  // ─── Write helpers ────────────────────────────────────────────

  async write(data: Buffer): Promise<void> {
    if (!this.conn) throw new Error("Not connected");
    const toSend = this.isCC51_ ? data : transCodeBlob(data);
    return new Promise((resolve, reject) => {
      this.conn!.send(toSend, this.addr.port, this.addr.ip, (err) => {
        if (err) reject(err); else resolve();
      });
    });
  }

  async writeDTLS(payload: Buffer, channel: number): Promise<void> {
    const frame = this.isCC51_ ? this.msgTxDataCC51(payload, channel) : this.msgTxData(payload, channel);
    return this.write(frame);
  }

  private async writeAndWait(req: Buffer, ok: (res: Buffer) => boolean): Promise<Buffer> {
    return new Promise<Buffer>((resolve, reject) => {
      const deadline = Date.now() + 5000;
      let interval: ReturnType<typeof setInterval>;

      const send = () => {
        if (Date.now() > deadline) {
          cleanup();
          reject(new Error("writeAndWait timeout"));
          return;
        }
        this.write(req).catch(() => {});
      };

      const cleanup = () => {
        clearInterval(interval);
        this.conn!.removeListener("message", onMsg);
      };

      const onMsg = (msg: Buffer, rinfo: dgram.RemoteInfo) => {
        if (rinfo.address !== this.addr.ip) return;

        let res: Buffer;
        if (this.isCC51_) {
          res = msg;
        } else {
          res = reverseTransCodeBlob(msg);
        }

        if (ok(res)) {
          this.addr.port = rinfo.port;
          cleanup();
          resolve(res);
        }
      };

      this.conn!.on("message", onMsg);
      interval = setInterval(send, 1000);
      send(); // send immediately
    });
  }

  // ─── Message builders ─────────────────────────────────────────

  private msgDisco(stage: number): Buffer {
    const b = Buffer.alloc(HEADER_SIZE + DISCO_BODY_SIZE);
    // Marker + mode
    b[0] = 0x04; b[1] = 0x02; b[2] = 0x1a; b[3] = 0x02;
    b.writeUInt16LE(DISCO_BODY_SIZE, 4);
    b.writeUInt16LE(CMD_DISCO_REQ, 8);
    b.writeUInt16LE(0x0021, 10);
    
    const body = b.subarray(HEADER_SIZE);
    Buffer.from(this.uid, "ascii").copy(body, 0);
    SDK_VERSION_42.copy(body, 36);
    this.sid.copy(body, 40);
    body[48] = stage;
    
    if (stage === 1 && this.authKey.length > 0) {
      Buffer.from(this.authKey, "ascii").copy(body, 58);
    }
    
    return b;
  }

  private msgDiscoCC51(seq: number, ticket: number, isResponse: boolean): Buffer {
    const b = Buffer.alloc(PACKET_SIZE_CC51);
    b[0] = 0x51; b[1] = 0xcc;
    b.writeUInt16LE(CMD_DISCO_CC51, 4);
    b.writeUInt16LE(PAYLOAD_SIZE_CC51, 6);
    if (isResponse) {
      b.writeUInt16LE(0xffff, 8);
    }
    b.writeUInt16LE(seq, 12);
    b.writeUInt16LE(ticket, 14);
    this.sid.copy(b, 16, 0, 8);
    SDK_VERSION_43.copy(b, 24);
    b[28] = 0x1d;

    // HMAC-SHA1 auth
    const hmacKey = Buffer.concat([Buffer.from(this.uid, "ascii"), Buffer.from(this.authKey, "ascii")]);
    const h = createHmac("sha1", hmacKey);
    h.update(b.subarray(0, 32));
    h.digest().copy(b, 32);
    
    return b;
  }

  private msgSession(): Buffer {
    const b = Buffer.alloc(HEADER_SIZE + SESSION_BODY);
    b[0] = 0x04; b[1] = 0x02; b[2] = 0x1a; b[3] = 0x02;
    b.writeUInt16LE(SESSION_BODY, 4);
    b.writeUInt16LE(CMD_SESSION_REQ, 8);
    b.writeUInt16LE(0x0033, 10);
    
    const body = b.subarray(HEADER_SIZE);
    Buffer.from(this.uid, "ascii").copy(body, 0);
    this.sid.copy(body, 20);
    body.writeUInt32LE(Math.floor(Date.now() / 1000), 32);
    
    return b;
  }

  private msgKeepalive(incoming: Buffer): Buffer {
    const b = Buffer.alloc(24);
    b[0] = 0x04; b[1] = 0x02; b[2] = 0x1a; b[3] = 0x0a;
    b.writeUInt16LE(8, 4);
    b.writeUInt16LE(CMD_KEEPALIVE_REQ, 8);
    b.writeUInt16LE(0x0021, 10);
    if (incoming.length >= 8) {
      incoming.copy(b, 16, 0, 8);
    }
    return b;
  }

  private msgKeepaliveCC51(): Buffer {
    this.kaSeq += 2;
    const b = Buffer.alloc(KEEPALIVE_SIZE_CC51);
    b[0] = 0x51; b[1] = 0xcc;
    b.writeUInt16LE(CMD_KEEPALIVE_CC51, 4);
    b.writeUInt16LE(0x0024, 6);
    b.writeUInt32LE(this.kaSeq, 16);
    this.sid.copy(b, 20, 0, 8);
    
    const hmacKey = Buffer.concat([Buffer.from(this.uid, "ascii"), Buffer.from(this.authKey, "ascii")]);
    const h = createHmac("sha1", hmacKey);
    h.update(b.subarray(0, 28));
    h.digest().copy(b, 28);
    
    return b;
  }

  private msgTxData(payload: Buffer, channel: number): Buffer {
    const bodySize = 12 + payload.length;
    const b = Buffer.alloc(16 + bodySize);
    b[0] = 0x04; b[1] = 0x02; b[2] = 0x1a; b[3] = 0x0b;
    b.writeUInt16LE(bodySize, 4);
    // ADR-023 followup 2026-05-11: mask seq to 16 bits to prevent
    // RangeError after ~65535 packets per camera (UInt16 overflow).
    // The PRE-bundled npm-published artifact (built from an older
    // checkpoint where this field was named `txSeq`) shipped without
    // this mask; the live patch lives at
    // ~/.scrypted/volume/plugins/@apocaliss92/scrypted-wyze-native/zip/unzipped/main.nodejs.js
    // See ~/Developer/homelab-scrypted/audit/log-spam-2026-05-10.md.
    b.writeUInt16LE(this.seq & 0xFFFF, 6);
    this.seq++;
    b.writeUInt16LE(CMD_DATA_TX, 8);
    b.writeUInt16LE(0x0021, 10);
    this.sid.copy(b, 12, 0, 2);
    b[14] = channel;
    b[15] = 0x01;
    b.writeUInt32LE(0x0000000c, 16);
    this.sid.copy(b, 20, 0, 8);
    payload.copy(b, 28);
    return b;
  }

  private msgTxDataCC51(payload: Buffer, channel: number): Buffer {
    const payloadSize = 16 + payload.length + AUTH_SIZE_CC51;
    const b = Buffer.alloc(HEADER_SIZE_CC51 + payload.length + AUTH_SIZE_CC51);
    b[0] = 0x51; b[1] = 0xcc;
    b.writeUInt16LE(CMD_DTLS_CC51, 4);
    b.writeUInt16LE(payloadSize, 6);
    b.writeUInt16LE(0x0010 | (channel << 8), 12);
    b.writeUInt16LE(this.ticket, 14);
    this.sid.copy(b, 16, 0, 8);
    b.writeUInt32LE(1, 24);
    payload.copy(b, HEADER_SIZE_CC51);
    
    const hmacKey = Buffer.concat([Buffer.from(this.uid, "ascii"), Buffer.from(this.authKey, "ascii")]);
    const h = createHmac("sha1", hmacKey);
    h.update(b.subarray(0, HEADER_SIZE_CC51));
    h.digest().copy(b, HEADER_SIZE_CC51 + payload.length);
    
    return b;
  }

  msgAVLogin(magic: number, size: number, flags: number, randomID: Buffer): Buffer {
    const b = Buffer.alloc(size);
    b.writeUInt16LE(magic, 0);
    b.writeUInt16LE(PROTO_VERSION, 2);
    b.writeUInt16LE(size - 24, 16);
    b.writeUInt16LE(flags, 18);
    randomID.copy(b, 20, 0, 4);
    Buffer.from("admin", "ascii").copy(b, 24);
    Buffer.from(this.enr, "ascii").copy(b, 280);
    b.writeUInt32LE(4, 540);
    b.writeUInt32LE(DEFAULT_CAPS, 552);
    return b;
  }

  msgACK(): Buffer {
    this.ackFlags++;
    const b = Buffer.alloc(24);
    b.writeUInt16LE(MAGIC_ACK, 0);
    b.writeUInt16LE(PROTO_VERSION, 2);
    b.writeUInt32LE(this.avSeq, 4);
    this.avSeq++;
    b.writeUInt16LE(this.rxSeqStart, 8);
    b.writeUInt16LE(this.rxSeqEnd, 10);
    if (this.rxSeqInit) {
      this.rxSeqStart = this.rxSeqEnd;
    }
    b.writeUInt16LE(this.ackFlags, 12);
    b.writeUInt32LE(this.ackFlags << 16, 16);
    b.writeUInt16LE(Date.now() & 0xffff, 20);
    return b;
  }

  msgIOCtrl(payload: Buffer): Buffer {
    const b = Buffer.alloc(40 + payload.length);
    b.writeUInt16LE(PROTO_VERSION, 0);
    b.writeUInt16LE(PROTO_VERSION, 2);
    b.writeUInt32LE(this.avSeq, 4);
    this.avSeq++;
    b.writeUInt16LE(MAGIC_IOCTRL, 16);
    b.writeUInt16LE(this.seqCmd, 18);
    b.writeUInt32LE(1, 20);
    b.writeUInt32LE(payload.length + 4, 24);
    b.writeUInt32LE(this.seqCmd, 28);
    b[37] = 0x01;
    payload.copy(b, 40);
    this.seqCmd++;
    return b;
  }

  // ─── Public API ───────────────────────────────────────────────

  getFrameHandler(): FrameHandler {
    return this.frames;
  }

  getSid(): Buffer {
    return this.sid;
  }

  getPSK(): Buffer {
    return this.psk;
  }

  getAddr(): { ip: string; port: number } {
    return { ...this.addr };
  }

  getUDPSocket(): dgram.Socket | null {
    return this.conn;
  }

  close(): void {
    this.closed = true;
    this.frames.close();
    if (this.conn) {
      try { this.conn.close(); } catch {}
      this.conn = null;
    }
  }
}
