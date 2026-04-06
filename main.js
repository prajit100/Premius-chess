// Premium Canvas Chess — single-file module with clean class boundaries.
// No external chessboard libraries; everything renders via Canvas.
// AI: minimax + alpha-beta, iterative deepening, transposition table.
//
// Authoring style: production-friendly, readable, and robust.
// ------------------------------------------------------------

// ======================= Utilities ==========================
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const nowMs = () => performance.now();
const sleep = (ms) => new Promise(r => setTimeout(r, ms));
const rand01 = () => (Math.random());
const lerp = (a,b,t)=>a+(b-a)*t;

function sqToFile(sq){ return sq & 7; }
function sqToRank(sq){ return sq >> 3; }
function inBounds(f,r){ return f>=0 && f<8 && r>=0 && r<8; }
function frToSq(f,r){ return (r<<3)|f; }
function sqToAlg(sq){
  const f = sqToFile(sq), r = sqToRank(sq);
  return String.fromCharCode(97+f) + (r+1);
}
function opposite(c){ return c==='w'?'b':'w'; }

function popcount32(x){
  x = x - ((x >>> 1) & 0x55555555);
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  return (((x + (x >>> 4)) & 0x0F0F0F0F) * 0x01010101) >>> 24;
}

// ======================= Chess Core =========================

// Piece encoding: 0 empty; 1..6 white pawn..king; 9..14 black pawn..king
// type = p,n,b,r,q,k -> 1..6 ; color bit: +8 for black
const EMPTY=0;
const WP=1, WN=2, WB=3, WR=4, WQ=5, WK=6;
const BP=9, BN=10, BB=11, BR=12, BQ=13, BK=14;

const PIECE_TO_CHAR = {
  [WP]:'P',[WN]:'N',[WB]:'B',[WR]:'R',[WQ]:'Q',[WK]:'K',
  [BP]:'p',[BN]:'n',[BB]:'b',[BR]:'r',[BQ]:'q',[BK]:'k'
};
const CHAR_TO_PIECE = {
  'P':WP,'N':WN,'B':WB,'R':WR,'Q':WQ,'K':WK,
  'p':BP,'n':BN,'b':BB,'r':BR,'q':BQ,'k':BK
};
function isWhite(p){ return p>=1 && p<=6; }
function isBlack(p){ return p>=9 && p<=14; }
function colorOf(p){ return isWhite(p)?'w':(isBlack(p)?'b':null); }
function typeOf(p){ if(p===0) return 0; return (p & 7); } // 1..6
function makePiece(color, type){ return color==='w'?type:(type|8); }

const MOVE_FLAGS = {
  QUIET:0,
  CAPTURE:1<<0,
  EP:1<<1,
  CASTLE:1<<2,
  PROMO:1<<3,
  PAWN2:1<<4,
};

class Move {
  constructor(from, to, piece, captured=EMPTY, promo=0, flags=0){
    this.from=from; this.to=to; this.piece=piece; this.captured=captured; this.promo=promo; this.flags=flags;
    this.san = null;
  }
}

class Zobrist {
  constructor(seed=0xC0FFEE){
    // Deterministic RNG
    let s = seed >>> 0;
    const rnd32 = () => {
      // xorshift32
      s ^= (s << 13) >>> 0;
      s ^= (s >>> 17) >>> 0;
      s ^= (s << 5) >>> 0;
      return s >>> 0;
    };
    // use BigInt for safe 64-bit
    this.piece = Array.from({length:15}, ()=>Array.from({length:64}, ()=>0n));
    for(let p=0;p<15;p++){
      for(let sq=0;sq<64;sq++){
        const hi = BigInt(rnd32());
        const lo = BigInt(rnd32());
        this.piece[p][sq] = (hi<<32n) ^ lo;
      }
    }
    this.castle = Array.from({length:16}, ()=>0n);
    for(let i=0;i<16;i++){
      const hi = BigInt(rnd32()), lo = BigInt(rnd32());
      this.castle[i] = (hi<<32n) ^ lo;
    }
    this.epFile = Array.from({length:9}, ()=>0n); // 0..7 file, 8 = none
    for(let i=0;i<9;i++){
      const hi = BigInt(rnd32()), lo = BigInt(rnd32());
      this.epFile[i] = (hi<<32n) ^ lo;
    }
    const hi = BigInt(rnd32()), lo = BigInt(rnd32());
    this.side = (hi<<32n) ^ lo;
  }
}

class Chess {
  constructor(){
    this.zob = new Zobrist();
    this.reset();
  }

  reset(){
    this.board = new Array(64).fill(EMPTY);
    this.sideToMove = 'w';
    this.castleRights = 0b1111; // KQkq bits: 1=WK,2=WQ,4=BK,8=BQ
    this.epSquare = -1;
    this.halfmoveClock = 0;
    this.fullmoveNumber = 1;
    this.history = [];
    this.hash = 0n;
    this.repetition = new Map(); // hash string -> count
    this.loadFEN("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
  }

  cloneLite(){
    // For search speed: shallow clone arrays
    const c = Object.create(Chess.prototype);
    c.zob = this.zob;
    c.board = this.board.slice();
    c.sideToMove = this.sideToMove;
    c.castleRights = this.castleRights;
    c.epSquare = this.epSquare;
    c.halfmoveClock = this.halfmoveClock;
    c.fullmoveNumber = this.fullmoveNumber;
    c.history = this.history.slice();
    c.hash = this.hash;
    c.repetition = new Map(this.repetition);
    return c;
  }

  loadFEN(fen){
    const parts = fen.trim().split(/\s+/);
    const rows = parts[0].split('/');
    this.board.fill(EMPTY);
    let sq = 56;
    for(const row of rows){
      let file=0;
      for(const ch of row){
        if(/[1-8]/.test(ch)){
          file += parseInt(ch,10);
        }else{
          const p = CHAR_TO_PIECE[ch];
          this.board[sq+file]=p;
          file++;
        }
      }
      sq -= 8;
    }
    this.sideToMove = parts[1]==='b'?'b':'w';
    this.castleRights = 0;
    if(parts[2].includes('K')) this.castleRights |= 1;
    if(parts[2].includes('Q')) this.castleRights |= 2;
    if(parts[2].includes('k')) this.castleRights |= 4;
    if(parts[2].includes('q')) this.castleRights |= 8;
    this.epSquare = (parts[3] === '-' ? -1 : this.algToSq(parts[3]));
    this.halfmoveClock = parseInt(parts[4]||'0',10);
    this.fullmoveNumber = parseInt(parts[5]||'1',10);

    this.history = [];
    this.repetition = new Map();
    this.hash = this.computeHash();
    this._bumpRepetition(this.hash, +1);
  }

  fen(){
    let out='';
    for(let r=7;r>=0;r--){
      let empty=0;
      for(let f=0;f<8;f++){
        const sq=frToSq(f,r);
        const p=this.board[sq];
        if(p===EMPTY){ empty++; }
        else{
          if(empty){ out+=empty; empty=0; }
          out+=PIECE_TO_CHAR[p];
        }
      }
      if(empty) out+=empty;
      if(r) out+='/';
    }
    out+=' ';
    out+=this.sideToMove;
    out+=' ';
    let cr='';
    if(this.castleRights&1) cr+='K';
    if(this.castleRights&2) cr+='Q';
    if(this.castleRights&4) cr+='k';
    if(this.castleRights&8) cr+='q';
    out+=cr||'-';
    out+=' ';
    out+=(this.epSquare===-1?'-':sqToAlg(this.epSquare));
    out+=' ';
    out+=this.halfmoveClock;
    out+=' ';
    out+=this.fullmoveNumber;
    return out;
  }

  algToSq(alg){
    const f=alg.charCodeAt(0)-97;
    const r=parseInt(alg[1],10)-1;
    return frToSq(f,r);
  }

  computeHash(){
    let h=0n;
    for(let sq=0;sq<64;sq++){
      const p=this.board[sq];
      if(p!==EMPTY) h ^= this.zob.piece[p][sq];
    }
    h ^= this.zob.castle[this.castleRights & 15];
    const epFile = (this.epSquare===-1?8:sqToFile(this.epSquare));
    h ^= this.zob.epFile[epFile];
    if(this.sideToMove==='b') h ^= this.zob.side;
    return h;
  }

  _bumpRepetition(hash, delta){
    const k = hash.toString();
    const v = (this.repetition.get(k)||0) + delta;
    if(v<=0) this.repetition.delete(k);
    else this.repetition.set(k, v);
  }

  kingSquare(color){
    const target = (color==='w'?WK:BK);
    for(let i=0;i<64;i++) if(this.board[i]===target) return i;
    return -1;
  }

  // -------- Attack detection --------
  isSquareAttacked(sq, byColor){
    const b=this.board;
    const f=sqToFile(sq), r=sqToRank(sq);

    // pawns
    if(byColor==='w'){
      // white pawn attacks from r-1
      const r2=r-1;
      if(r2>=0){
        if(f-1>=0 && b[frToSq(f-1,r2)]===WP) return true;
        if(f+1<8 && b[frToSq(f+1,r2)]===WP) return true;
      }
    }else{
      const r2=r+1;
      if(r2<8){
        if(f-1>=0 && b[frToSq(f-1,r2)]===BP) return true;
        if(f+1<8 && b[frToSq(f+1,r2)]===BP) return true;
      }
    }

    // knights
    const knights = byColor==='w'?WN:BN;
    const N = [[1,2],[2,1],[-1,2],[-2,1],[1,-2],[2,-1],[-1,-2],[-2,-1]];
    for(const [df,dr] of N){
      const ff=f+df, rr=r+dr;
      if(inBounds(ff,rr) && b[frToSq(ff,rr)]===knights) return true;
    }

    // bishops / queens (diagonals)
    const bishop = byColor==='w'?WB:BB;
    const queen = byColor==='w'?WQ:BQ;
    const rook  = byColor==='w'?WR:BR;
    const king  = byColor==='w'?WK:BK;

    const diag = [[1,1],[1,-1],[-1,1],[-1,-1]];
    for(const [df,dr] of diag){
      let ff=f+df, rr=r+dr;
      while(inBounds(ff,rr)){
        const p=b[frToSq(ff,rr)];
        if(p!==EMPTY){
          if(p===bishop || p===queen) return true;
          break;
        }
        ff+=df; rr+=dr;
      }
    }

    // rooks / queens (orthogonal)
    const ortho = [[1,0],[-1,0],[0,1],[0,-1]];
    for(const [df,dr] of ortho){
      let ff=f+df, rr=r+dr;
      while(inBounds(ff,rr)){
        const p=b[frToSq(ff,rr)];
        if(p!==EMPTY){
          if(p===rook || p===queen) return true;
          break;
        }
        ff+=df; rr+=dr;
      }
    }

    // king adjacency
    const K = [[1,1],[1,0],[1,-1],[0,1],[0,-1],[-1,1],[-1,0],[-1,-1]];
    for(const [df,dr] of K){
      const ff=f+df, rr=r+dr;
      if(inBounds(ff,rr) && b[frToSq(ff,rr)]===king) return true;
    }

    return false;
  }

  inCheck(color){
    const ksq = this.kingSquare(color);
    if(ksq<0) return false;
    return this.isSquareAttacked(ksq, opposite(color));
  }

  // -------- Move generation (pseudo + legality) --------
  generateMoves({legal=true}={}){
    const moves = [];
    const side = this.sideToMove;
    for(let sq=0;sq<64;sq++){
      const p=this.board[sq];
      if(p===EMPTY) continue;
      if(colorOf(p)!==side) continue;
      this._genPieceMoves(sq,p,moves);
    }
    if(!legal) return moves;

    const legalMoves=[];
    for(const m of moves){
      this.makeMove(m);
      const ok = !this.inCheck(opposite(this.sideToMove)); // after makeMove, sideToMove flipped
      this.undoMove();
      if(ok) legalMoves.push(m);
    }
    return legalMoves;
  }

  _genPieceMoves(sq,p,moves){
    const side=this.sideToMove;
    const t=typeOf(p);
    if(t===1) return this._genPawn(sq,p,moves);
    if(t===2) return this._genKnight(sq,p,moves);
    if(t===3) return this._genBishop(sq,p,moves);
    if(t===4) return this._genRook(sq,p,moves);
    if(t===5) return this._genQueen(sq,p,moves);
    if(t===6) return this._genKing(sq,p,moves);
  }

  _genPawn(sq,p,moves){
    const side=colorOf(p);
    const f=sqToFile(sq), r=sqToRank(sq);
    const dir = (side==='w'?1:-1);
    const startRank = (side==='w'?1:6);
    const promoRank = (side==='w'?7:0);
    const oneR = r+dir;
    if(oneR>=0 && oneR<8){
      const oneSq=frToSq(f,oneR);
      if(this.board[oneSq]===EMPTY){
        if(oneR===promoRank){
          for(const pr of [5,4,3,2]){ // Q R B N (type codes)
            moves.push(new Move(sq, oneSq, p, EMPTY, makePiece(side, pr), MOVE_FLAGS.PROMO));
          }
        }else{
          moves.push(new Move(sq, oneSq, p, EMPTY, 0, MOVE_FLAGS.QUIET));
          // two
          if(r===startRank){
            const twoR=r+2*dir;
            const twoSq=frToSq(f,twoR);
            if(this.board[twoSq]===EMPTY){
              moves.push(new Move(sq, twoSq, p, EMPTY, 0, MOVE_FLAGS.PAWN2));
            }
          }
        }
      }
    }
    // captures
    for(const df of [-1,1]){
      const ff=f+df;
      if(ff<0||ff>=8) continue;
      const rr=r+dir;
      if(rr<0||rr>=8) continue;
      const to=frToSq(ff,rr);
      const target=this.board[to];
      if(target!==EMPTY && colorOf(target)!==side){
        if(rr===promoRank){
          for(const pr of [5,4,3,2]){
            moves.push(new Move(sq,to,p,target,makePiece(side,pr), MOVE_FLAGS.CAPTURE|MOVE_FLAGS.PROMO));
          }
        }else{
          moves.push(new Move(sq,to,p,target,0, MOVE_FLAGS.CAPTURE));
        }
      }
      // en passant
      if(this.epSquare===to){
        const capSq = frToSq(ff, r); // pawn behind target square
        const capPiece = this.board[capSq];
        if(capPiece!==EMPTY && typeOf(capPiece)===1 && colorOf(capPiece)!==side){
          moves.push(new Move(sq,to,p,capPiece,0, MOVE_FLAGS.CAPTURE|MOVE_FLAGS.EP));
        }
      }
    }
  }

  _genKnight(sq,p,moves){
    const side=colorOf(p);
    const f=sqToFile(sq), r=sqToRank(sq);
    const N = [[1,2],[2,1],[-1,2],[-2,1],[1,-2],[2,-1],[-1,-2],[-2,-1]];
    for(const [df,dr] of N){
      const ff=f+df, rr=r+dr;
      if(!inBounds(ff,rr)) continue;
      const to=frToSq(ff,rr);
      const t=this.board[to];
      if(t===EMPTY) moves.push(new Move(sq,to,p,EMPTY,0,MOVE_FLAGS.QUIET));
      else if(colorOf(t)!==side) moves.push(new Move(sq,to,p,t,0,MOVE_FLAGS.CAPTURE));
    }
  }

  _slideMoves(sq,p,moves,dirs){
    const side=colorOf(p);
    const f0=sqToFile(sq), r0=sqToRank(sq);
    for(const [df,dr] of dirs){
      let f=f0+df, r=r0+dr;
      while(inBounds(f,r)){
        const to=frToSq(f,r);
        const t=this.board[to];
        if(t===EMPTY){
          moves.push(new Move(sq,to,p,EMPTY,0,MOVE_FLAGS.QUIET));
        }else{
          if(colorOf(t)!==side) moves.push(new Move(sq,to,p,t,0,MOVE_FLAGS.CAPTURE));
          break;
        }
        f+=df; r+=dr;
      }
    }
  }

  _genBishop(sq,p,moves){
    this._slideMoves(sq,p,moves, [[1,1],[1,-1],[-1,1],[-1,-1]]);
  }
  _genRook(sq,p,moves){
    this._slideMoves(sq,p,moves, [[1,0],[-1,0],[0,1],[0,-1]]);
  }
  _genQueen(sq,p,moves){
    this._slideMoves(sq,p,moves, [[1,1],[1,-1],[-1,1],[-1,-1],[1,0],[-1,0],[0,1],[0,-1]]);
  }

  _genKing(sq,p,moves){
    const side=colorOf(p);
    const f=sqToFile(sq), r=sqToRank(sq);
    const K = [[1,1],[1,0],[1,-1],[0,1],[0,-1],[-1,1],[-1,0],[-1,-1]];
    for(const [df,dr] of K){
      const ff=f+df, rr=r+dr;
      if(!inBounds(ff,rr)) continue;
      const to=frToSq(ff,rr);
      const t=this.board[to];
      if(t===EMPTY) moves.push(new Move(sq,to,p,EMPTY,0,MOVE_FLAGS.QUIET));
      else if(colorOf(t)!==side) moves.push(new Move(sq,to,p,t,0,MOVE_FLAGS.CAPTURE));
    }
    // castling
    if(side==='w'){
      if((this.castleRights&1) && this._canCastle('w','K')) moves.push(new Move(sq, frToSq(6,0), p, EMPTY,0, MOVE_FLAGS.CASTLE));
      if((this.castleRights&2) && this._canCastle('w','Q')) moves.push(new Move(sq, frToSq(2,0), p, EMPTY,0, MOVE_FLAGS.CASTLE));
    }else{
      if((this.castleRights&4) && this._canCastle('b','K')) moves.push(new Move(sq, frToSq(6,7), p, EMPTY,0, MOVE_FLAGS.CASTLE));
      if((this.castleRights&8) && this._canCastle('b','Q')) moves.push(new Move(sq, frToSq(2,7), p, EMPTY,0, MOVE_FLAGS.CASTLE));
    }
  }

  _canCastle(color, side){
    // side: 'K' or 'Q'
    const rank = (color==='w'?0:7);
    const kingSq = frToSq(4,rank);
    const rookSq = (side==='K'?frToSq(7,rank):frToSq(0,rank));
    const between = (side==='K'?[frToSq(5,rank),frToSq(6,rank)]:[frToSq(1,rank),frToSq(2,rank),frToSq(3,rank)]);
    // pieces correct
    if(this.board[kingSq] !== (color==='w'?WK:BK)) return false;
    if(this.board[rookSq] !== (color==='w'?WR:BR)) return false;
    // empty between
    for(const s of between) if(this.board[s]!==EMPTY) return false;
    // not in check and squares not attacked
    if(this.isSquareAttacked(kingSq, opposite(color))) return false;
    const passSquares = (side==='K'?[frToSq(5,rank), frToSq(6,rank)]:[frToSq(3,rank), frToSq(2,rank)]);
    for(const s of passSquares){
      if(this.isSquareAttacked(s, opposite(color))) return false;
    }
    return true;
  }

  // -------- Make / Undo --------
  makeMove(m){
    // Save state snapshot
    const st = {
      move:m,
      castleRights: this.castleRights,
      epSquare: this.epSquare,
      halfmoveClock: this.halfmoveClock,
      fullmoveNumber: this.fullmoveNumber,
      hash: this.hash
    };

    // update repetition: leaving current position
    this._bumpRepetition(this.hash, -1);

    const side = this.sideToMove;
    const opp = opposite(side);
    const b=this.board;

    // Halfmove clock
    if(typeOf(m.piece)===1 || (m.flags & MOVE_FLAGS.CAPTURE)) this.halfmoveClock = 0;
    else this.halfmoveClock++;

    // Clear EP
    this.epSquare = -1;

    // Move piece
    b[m.from] = EMPTY;

    // Special: en passant capture
    if(m.flags & MOVE_FLAGS.EP){
      const toF = sqToFile(m.to);
      const fromR = sqToRank(m.from);
      const capSq = frToSq(toF, fromR);
      st.epCapturedSq = capSq;
      b[capSq] = EMPTY;
    }

    // Special: castling rook move
    if(m.flags & MOVE_FLAGS.CASTLE){
      const rank = (side==='w'?0:7);
      if(m.to === frToSq(6,rank)){ // king side
        const rookFrom=frToSq(7,rank), rookTo=frToSq(5,rank);
        st.castleRook = {from: rookFrom, to: rookTo, piece: b[rookFrom]};
        b[rookFrom]=EMPTY;
        b[rookTo]= (side==='w'?WR:BR);
      }else if(m.to === frToSq(2,rank)){ // queen side
        const rookFrom=frToSq(0,rank), rookTo=frToSq(3,rank);
        st.castleRook = {from: rookFrom, to: rookTo, piece: b[rookFrom]};
        b[rookFrom]=EMPTY;
        b[rookTo]= (side==='w'?WR:BR);
      }
    }

    // Handle capture on destination
    if(m.flags & MOVE_FLAGS.CAPTURE){
      // capture already accounted for EP separately
      if(!(m.flags & MOVE_FLAGS.EP)){
        st.captured = b[m.to];
      }
    }

    // Place moved piece (promotion changes piece)
    if(m.flags & MOVE_FLAGS.PROMO){
      b[m.to] = m.promo;
    }else{
      b[m.to] = m.piece;
    }

    // Update castling rights if king/rook moved or rook captured
    this._updateCastleRightsOnMove(m);

    // Set EP square if pawn double
    if(m.flags & MOVE_FLAGS.PAWN2){
      const rFrom = sqToRank(m.from);
      const rTo = sqToRank(m.to);
      const epR = (rFrom+rTo)/2;
      this.epSquare = frToSq(sqToFile(m.from), epR);
    }

    // Update fullmove
    if(side==='b') this.fullmoveNumber++;

    // Switch side
    this.sideToMove = opp;

    // Recompute hash incrementally (simple: recompute for correctness)
    this.hash = this.computeHash();

    this.history.push(st);

    // enter new position repetition
    this._bumpRepetition(this.hash, +1);

    return true;
  }

  _updateCastleRightsOnMove(m){
    const from=m.from, to=m.to;
    const p=m.piece;
    // king moved
    if(p===WK) this.castleRights &= ~3;
    if(p===BK) this.castleRights &= ~12;
    // rooks moved
    if(p===WR){
      if(from===frToSq(0,0)) this.castleRights &= ~2;
      if(from===frToSq(7,0)) this.castleRights &= ~1;
    }
    if(p===BR){
      if(from===frToSq(0,7)) this.castleRights &= ~8;
      if(from===frToSq(7,7)) this.castleRights &= ~4;
    }
    // rooks captured
    const capSq = (m.flags & MOVE_FLAGS.EP) ? (this.history.length?this.history[this.history.length-1]?.epCapturedSq:-1) : to;
    const capPiece = m.captured;
    // When capture flag is set, m.captured is set by generator; handle both sides by squares.
    if(m.flags & MOVE_FLAGS.CAPTURE){
      // if rook captured on its home square, remove rights
      if(to===frToSq(0,0)) this.castleRights &= ~2;
      if(to===frToSq(7,0)) this.castleRights &= ~1;
      if(to===frToSq(0,7)) this.castleRights &= ~8;
      if(to===frToSq(7,7)) this.castleRights &= ~4;
    }
  }

  undoMove(){
    if(!this.history.length) return null;
    const st = this.history.pop();

    // exit current repetition
    this._bumpRepetition(this.hash, -1);

    // restore
    this.castleRights = st.castleRights;
    this.epSquare = st.epSquare;
    this.halfmoveClock = st.halfmoveClock;
    this.fullmoveNumber = st.fullmoveNumber;
    this.sideToMove = opposite(this.sideToMove);

    const b=this.board;
    const m=st.move;

    // revert moved piece
    b[m.from] = m.piece;
    // destination restore
    if(m.flags & MOVE_FLAGS.PROMO){
      b[m.to] = (this.sideToMove==='w'?WP:BP);
    }else{
      b[m.to] = EMPTY;
    }

    // restore capture
    if(m.flags & MOVE_FLAGS.CAPTURE){
      if(m.flags & MOVE_FLAGS.EP){
        // restore captured pawn behind
        const toF = sqToFile(m.to);
        const fromR = sqToRank(m.from);
        const capSq = frToSq(toF, fromR);
        b[capSq] = (this.sideToMove==='w'?BP:WP);
      }else{
        b[m.to] = m.captured;
      }
    }

    // restore castling rook
    if(m.flags & MOVE_FLAGS.CASTLE){
      const rank = (this.sideToMove==='w'?0:7);
      if(m.to === frToSq(6,rank)){
        b[frToSq(7,rank)] = (this.sideToMove==='w'?WR:BR);
        b[frToSq(5,rank)] = EMPTY;
      }else if(m.to === frToSq(2,rank)){
        b[frToSq(0,rank)] = (this.sideToMove==='w'?WR:BR);
        b[frToSq(3,rank)] = EMPTY;
      }
      // king is already restored above
      b[m.to] = EMPTY;
    }

    this.hash = st.hash;

    // enter repetition of restored
    this._bumpRepetition(this.hash, +1);

    return st.move;
  }

  // -------- Draw & game status --------
  isThreefold(){
    const k=this.hash.toString();
    return (this.repetition.get(k)||0) >= 3;
  }

  isFiftyMove(){
    return this.halfmoveClock >= 100;
  }

  insufficientMaterial(){
    // Basic insufficient material detection:
    // - K vs K
    // - K+N vs K
    // - K+B vs K
    // - K+B vs K+B with bishops on same color
    const pieces=[];
    for(let sq=0;sq<64;sq++){
      const p=this.board[sq];
      if(p!==EMPTY) pieces.push({p,sq});
    }
    // remove kings
    const nonKings = pieces.filter(x => typeOf(x.p)!==6);
    // pawns/queens/rooks => sufficient
    for(const x of nonKings){
      const t=typeOf(x.p);
      if(t===1||t===4||t===5) return false;
    }
    // count bishops/knights
    const bishops = nonKings.filter(x=>typeOf(x.p)===3);
    const knights = nonKings.filter(x=>typeOf(x.p)===2);
    // if any side has 2 minors -> usually sufficient except 2 knights vs king (still insufficient unless help by pawn, but no pawns here)
    if(nonKings.length===0) return true;
    if(nonKings.length===1){
      // single bishop or knight
      return true;
    }
    if(nonKings.length===2 && bishops.length===2){
      // bishops on same color?
      const c0 = (sqToFile(bishops[0].sq)+sqToRank(bishops[0].sq))%2;
      const c1 = (sqToFile(bishops[1].sq)+sqToRank(bishops[1].sq))%2;
      return c0===c1;
    }
    return false;
  }

  legalMoves(){
    return this.generateMoves({legal:true});
  }

  gameStatus(){
    const legal = this.legalMoves();
    const inCheck = this.inCheck(this.sideToMove);
    if(legal.length===0){
      if(inCheck) return {over:true, result: (this.sideToMove==='w'?'0-1':'1-0'), reason:'checkmate'};
      else return {over:true, result:'1/2-1/2', reason:'stalemate'};
    }
    if(this.isThreefold()) return {over:true, result:'1/2-1/2', reason:'threefold repetition'};
    if(this.isFiftyMove()) return {over:true, result:'1/2-1/2', reason:'50-move rule'};
    if(this.insufficientMaterial()) return {over:true, result:'1/2-1/2', reason:'insufficient material'};
    return {over:false, inCheck};
  }

  // -------- SAN generation --------
  moveToSAN(m){
    // Needs to know legality and check/mate after move.
    // We'll generate SAN relative to current position (before move).
    const side=this.sideToMove;
    const pieceType = typeOf(m.piece);
    const isCapture = (m.flags & MOVE_FLAGS.CAPTURE) !== 0;
    const toAlg = sqToAlg(m.to);

    // castling
    if(m.flags & MOVE_FLAGS.CASTLE){
      const rank = (side==='w'?0:7);
      const san = (m.to===frToSq(6,rank)) ? "O-O" : "O-O-O";
      // apply temporarily to check/mate markers
      this.makeMove(m);
      const st = this.gameStatus();
      const suffix = st.over && st.reason==='checkmate' ? "#" : (st.inCheck?"+":"");
      this.undoMove();
      return san + suffix;
    }

    let san='';
    const pieceLetter = (pieceType===1 ? '' : "NBRQK"[pieceType-2]);
    san += pieceLetter;

    // disambiguation if not pawn and not king
    if(pieceType!==1){
      const all = this.generateMoves({legal:true}).filter(x =>
        x.to===m.to && x.piece===m.piece && x.from!==m.from
      );
      if(all.length){
        const fromFile = sqToFile(m.from);
        const fromRank = sqToRank(m.from);
        const needFile = !all.every(x=>sqToFile(x.from)!==fromFile);
        const needRank = !all.every(x=>sqToRank(x.from)!==fromRank);
        if(needFile) san += String.fromCharCode(97+fromFile);
        if(needRank) san += String(fromRank+1);
        if(!needFile && !needRank){
          // default to file
          san += String.fromCharCode(97+fromFile);
        }
      }
    }else{
      // pawn capture includes file
      if(isCapture){
        san += String.fromCharCode(97+sqToFile(m.from));
      }
    }

    if(isCapture) san += "x";
    san += toAlg;

    if(m.flags & MOVE_FLAGS.PROMO){
      const promoType = typeOf(m.promo);
      const letter = " PNBRQK"[promoType]; // promoType 2..5
      san += "=" + letter.trim();
    }

    // check/mate markers
    this.makeMove(m);
    const st = this.gameStatus();
    const suffix = st.over && st.reason==='checkmate' ? "#" : (st.inCheck?"+":"");
    this.undoMove();

    return san + suffix;
  }
}

// ======================= Evaluation =========================

const PIECE_VALUE = {
  1:100, 2:320, 3:330, 4:500, 5:900, 6:0
};

// Piece-square tables (from white perspective). Values are centipawns.
// Kept moderate for speed + stability.
const PST = {
  P: [
     0, 0, 0, 0, 0, 0, 0, 0,
    50,50,50,50,50,50,50,50,
    10,10,20,30,30,20,10,10,
     6, 6,10,25,25,10, 6, 6,
     2, 2, 5,18,18, 5, 2, 2,
     0, 0, 0, 6, 6, 0, 0, 0,
     0, 0, 0,-8,-8, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0
  ],
  N: [
   -40,-25,-20,-18,-18,-20,-25,-40,
   -25,-10,  0,  5,  5,  0,-10,-25,
   -20,  5, 12, 15, 15, 12,  5,-20,
   -18,  8, 15, 20, 20, 15,  8,-18,
   -18,  6, 14, 18, 18, 14,  6,-18,
   -20,  2, 10, 12, 12, 10,  2,-20,
   -25,-10,  0,  3,  3,  0,-10,-25,
   -40,-25,-20,-18,-18,-20,-25,-40
  ],
  B: [
   -25,-12,-10,-10,-10,-10,-12,-25,
   -12,  2,  5,  8,  8,  5,  2,-12,
   -10,  6, 10, 12, 12, 10,  6,-10,
   -10,  8, 12, 15, 15, 12,  8,-10,
   -10,  8, 12, 15, 15, 12,  8,-10,
   -10,  6, 10, 12, 12, 10,  6,-10,
   -12,  2,  5,  8,  8,  5,  2,-12,
   -25,-12,-10,-10,-10,-10,-12,-25
  ],
  R: [
     0, 0, 5,10,10, 5, 0, 0,
    -4, 0, 2, 8, 8, 2, 0,-4,
    -4, 0, 2, 6, 6, 2, 0,-4,
    -4, 0, 2, 6, 6, 2, 0,-4,
    -4, 0, 2, 6, 6, 2, 0,-4,
    -4, 0, 2, 6, 6, 2, 0,-4,
     8,10,10,10,10,10,10, 8,
     0, 0, 0, 4, 4, 0, 0, 0
  ],
  Q: [
   -10,-8,-6,-4,-4,-6,-8,-10,
    -8,-2, 0, 2, 2, 0,-2,-8,
    -6, 0, 2, 4, 4, 2, 0,-6,
    -4, 2, 4, 6, 6, 4, 2,-4,
    -4, 2, 4, 6, 6, 4, 2,-4,
    -6, 0, 2, 4, 4, 2, 0,-6,
    -8,-2, 0, 2, 2, 0,-2,-8,
   -10,-8,-6,-4,-4,-6,-8,-10
  ],
  K: [
   -30,-25,-20,-18,-18,-20,-25,-30,
   -25,-20,-12,-10,-10,-12,-20,-25,
   -20,-12,-10, -5, -5,-10,-12,-20,
   -18,-10, -5,  0,  0, -5,-10,-18,
   -18,-10, -5,  0,  0, -5,-10,-18,
   -20,-12,-10, -5, -5,-10,-12,-20,
   -25,-20,-12,-10,-10,-12,-20,-25,
   -30,-25,-20,-18,-18,-20,-25,-30
  ],
  K_END: [
   -50,-35,-25,-20,-20,-25,-35,-50,
   -35,-18,-10, -6, -6,-10,-18,-35,
   -25,-10,  0,  8,  8,  0,-10,-25,
   -20, -6,  8, 16, 16,  8, -6,-20,
   -20, -6,  8, 16, 16,  8, -6,-20,
   -25,-10,  0,  8,  8,  0,-10,-25,
   -35,-18,-10, -6, -6,-10,-18,-35,
   -50,-35,-25,-20,-20,-25,-35,-50
  ]
};

function mirrorSq(sq){ // mirror vertically for black
  const f=sqToFile(sq), r=sqToRank(sq);
  return frToSq(f, 7-r);
}

class Evaluator {
  constructor(){
    // precompute pawn file masks for basic structure
    this.fileMask = Array.from({length:8}, (_,f)=> {
      let mask=0;
      for(let r=0;r<8;r++) mask |= (1 << (r*8+f));
      return mask;
    });
  }

  evaluate(chess){
    // returns score from side to move perspective (+ good for sideToMove)
    const b=chess.board;
    let material=0, pst=0;
    let wPieces=0, bPieces=0;
    let wMinor=0, bMinor=0;
    let wKingSq=-1, bKingSq=-1;

    // endgame phase
    let phase=0; // higher => midgame
    for(let sq=0;sq<64;sq++){
      const p=b[sq];
      if(p===EMPTY) continue;
      const c=colorOf(p);
      const t=typeOf(p);
      if(t===6){
        if(c==='w') wKingSq=sq; else bKingSq=sq;
        continue;
      }
      const val = PIECE_VALUE[t];
      if(c==='w'){ material += val; wPieces++; if(t===2||t===3) wMinor++; }
      else { material -= val; bPieces++; if(t===2||t===3) bMinor++; }
      // phase weights
      if(t===5) phase += 4;
      if(t===4) phase += 2;
      if(t===3||t===2) phase += 1;

      // PST
      const idx = (c==='w'?sq:mirrorSq(sq));
      if(t===1) pst += (c==='w'? PST.P[idx] : -PST.P[idx]);
      else if(t===2) pst += (c==='w'? PST.N[idx] : -PST.N[idx]);
      else if(t===3) pst += (c==='w'? PST.B[idx] : -PST.B[idx]);
      else if(t===4) pst += (c==='w'? PST.R[idx] : -PST.R[idx]);
      else if(t===5) pst += (c==='w'? PST.Q[idx] : -PST.Q[idx]);
    }

    // King PST blended (endgame: king activity)
    const phaseClamped = clamp(phase, 0, 16);
    const endT = 1 - (phaseClamped/16);
    if(wKingSq>=0){
      const idx = wKingSq;
      const mid = PST.K[idx];
      const end = PST.K_END[idx];
      pst += Math.round(lerp(mid,end,endT));
    }
    if(bKingSq>=0){
      const idx = mirrorSq(bKingSq);
      const mid = PST.K[idx];
      const end = PST.K_END[idx];
      pst -= Math.round(lerp(mid,end,endT));
    }

    // Mobility (cheap): count legal moves for both sides at low cost (pseudo legal ok)
    const stm = chess.sideToMove;
    let mobW=0, mobB=0;
    chess.sideToMove='w'; mobW = chess.generateMoves({legal:false}).length;
    chess.sideToMove='b'; mobB = chess.generateMoves({legal:false}).length;
    chess.sideToMove=stm;
    const mobility = (mobW - mobB) * 2;

    // Pawn structure basics (doubled, isolated)
    // We'll do a light heuristic: penalty per doubled pawn, isolated pawn.
    const pawnFilesW = new Array(8).fill(0);
    const pawnFilesB = new Array(8).fill(0);
    for(let sq=0;sq<64;sq++){
      const p=b[sq];
      if(p===WP) pawnFilesW[sqToFile(sq)]++;
      else if(p===BP) pawnFilesB[sqToFile(sq)]++;
    }
    let pawnStruct=0;
    for(let f=0;f<8;f++){
      if(pawnFilesW[f]>1) pawnStruct -= (pawnFilesW[f]-1)*12;
      if(pawnFilesB[f]>1) pawnStruct += (pawnFilesB[f]-1)*12;
      // isolated
      const wIso = pawnFilesW[f]>0 && (pawnFilesW[f-1]||0)===0 && (pawnFilesW[f+1]||0)===0;
      const bIso = pawnFilesB[f]>0 && (pawnFilesB[f-1]||0)===0 && (pawnFilesB[f+1]||0)===0;
      if(wIso) pawnStruct -= 10;
      if(bIso) pawnStruct += 10;
    }

    // King safety (very basic): penalty if king has moved away from castled-ish squares in midgame
    let kingSafety=0;
    if(endT < 0.65){ // midgame-ish
      if(wKingSq>=0){
        const wr=sqToRank(wKingSq), wf=sqToFile(wKingSq);
        // reward being on back rank and near corners after castling
        kingSafety += (wr===0 ? 8 : -10);
        kingSafety += (wf<=2 || wf>=5 ? 8 : -6);
      }
      if(bKingSq>=0){
        const br=sqToRank(bKingSq), bf=sqToFile(bKingSq);
        kingSafety -= (br===7 ? 8 : -10);
        kingSafety -= (bf<=2 || bf>=5 ? 8 : -6);
      }
    }

    let score = material + pst + mobility + pawnStruct + kingSafety;

    // Check bonus (small): encourages forcing lines
    if(chess.inCheck('w')) score -= 20;
    if(chess.inCheck('b')) score += 20;

    // perspective
    return (chess.sideToMove==='w' ? score : -score);
  }
}

// ========================= Engine ===========================

class TranspositionTable {
  constructor(maxEntries=500000){
    this.maxEntries = maxEntries;
    this.map = new Map(); // key: hash string -> {depth, score, flag, best}
    this.hits=0;
  }
  get(hash){ return this.map.get(hash.toString()); }
  set(hash, entry){
    if(this.map.size > this.maxEntries){
      // cheap prune: clear ~25%
      let i=0;
      for(const k of this.map.keys()){
        this.map.delete(k);
        if(++i>this.maxEntries*0.25) break;
      }
    }
    this.map.set(hash.toString(), entry);
  }
  clear(){ this.map.clear(); this.hits=0; }
}

const TT_FLAG = { EXACT:0, LOWER:1, UPPER:2 };

class Engine {
  constructor(){
    this.eval = new Evaluator();
    this.tt = new TranspositionTable(220000);
    this.stop=false;
    this.nodes=0;
    this.bestMove=null;
    this.bestScore=0;
    this.startTime=0;
    this.timeLimitMs=700;
    this.maxDepth=6;
    this.noise=0; // eval noise for easy
    this.useBook=false;
    this.openingBook = this._initBook();
  }

  _initBook(){
    // Very small, simple opening book: maps FEN piece placement + stm + castling + ep to a move in UCI.
    // This is optional but helps Hard/Expert feel more natural in the first moves.
    // We keep it tiny and deterministic to remain offline and simple.
    const book = new Map();
    const add = (fenPrefix, uciList) => book.set(fenPrefix, uciList);
    // Starting position (only prefix up to side/castling/ep):
    add("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq -", ["e2e4","d2d4","c2c4","g1f3"]);
    add("rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq -", ["c7c5","e7e5","e7e6","c7c6"]);
    add("rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b KQkq -", ["d7d5","g8f6","e7e6"]);
    add("rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w KQkq c6", ["g1f3","b1c3","d2d4"]);
    return book;
  }

  setDifficulty(level){
    const L = level;
    if(L==='easy'){
      this.maxDepth=3;
      this.timeLimitMs=240;
      this.noise=35;
      this.useBook=false;
    }else if(L==='medium'){
      this.maxDepth=4;
      this.timeLimitMs=450;
      this.noise=10;
      this.useBook=false;
    }else if(L==='hard'){
      this.maxDepth=6;
      this.timeLimitMs=900;
      this.noise=4;
      this.useBook=true;
    }else{ // expert
      this.maxDepth=8;
      this.timeLimitMs=1400;
      this.noise=0;
      this.useBook=true;
    }
  }

  async think(chess, onInfo){
    this.stop=false;
    this.nodes=0;
    this.bestMove=null;
    this.bestScore=-999999;
    this.startTime=nowMs();
    this.tt.hits=0;

    // Opening book (optional)
    if(this.useBook && chess.fullmoveNumber<=5){
      const prefix = chess.fen().split(' ').slice(0,4).join(' ');
      const list = this.openingBook.get(prefix);
      if(list && list.length){
        const uci = list[Math.floor(rand01()*list.length)];
        const move = this._uciToMove(chess, uci);
        if(move){
          if(onInfo) onInfo({depth:0, nodes:0, score:0, ttHits:0, book:true});
          await sleep(120);
          return move;
        }
      }
    }

    let best=null;
    let bestScore=-999999;

    for(let depth=1; depth<=this.maxDepth; depth++){
      const res = this._searchRoot(chess, depth);
      if(this.stop) break;
      best = res.bestMove;
      bestScore = res.bestScore;
      this.bestMove=best;
      this.bestScore=bestScore;
      if(onInfo) onInfo({depth, nodes:this.nodes, score:bestScore, ttHits:this.tt.hits, book:false});
      if(Math.abs(bestScore) > 90000) break; // mate found
      if(nowMs()-this.startTime > this.timeLimitMs) break;
      await Promise.resolve(); // yield
    }
    return best;
  }

  _timeUp(){ return (nowMs() - this.startTime) >= this.timeLimitMs; }

  _searchRoot(chess, depth){
    let alpha=-999999, beta=999999;
    let bestMove=null;
    let bestScore=-999999;

    const moves = chess.generateMoves({legal:true});
    // basic move ordering: captures first, then checks, then rest (we'll do cheap heuristics)
    moves.sort((a,b)=> this._moveOrderScore(chess,b) - this._moveOrderScore(chess,a));

    for(const m of moves){
      if(this._timeUp()){ this.stop=true; break; }
      chess.makeMove(m);
      const score = -this._alphabeta(chess, depth-1, -beta, -alpha);
      chess.undoMove();

      if(this.stop) break;

      if(score > bestScore){
        bestScore=score;
        bestMove=m;
      }
      if(score > alpha) alpha = score;
    }

    return {bestMove, bestScore};
  }

  _moveOrderScore(chess, m){
    // MVV-LVA style for captures; plus small bonus for promotions and castles.
    let s=0;
    if(m.flags & MOVE_FLAGS.PROMO) s += 800;
    if(m.flags & MOVE_FLAGS.CAPTURE){
      const capVal = PIECE_VALUE[typeOf(m.captured||chess.board[m.to]||0)] || 0;
      const moverVal = PIECE_VALUE[typeOf(m.piece)] || 0;
      s += 1000 + capVal*2 - moverVal;
    }
    if(m.flags & MOVE_FLAGS.CASTLE) s += 60;

    // cheap check bonus: make move and see if gives check (small and cached by TT helps)
    chess.makeMove(m);
    const givesCheck = chess.inCheck(chess.sideToMove); // after move, opponent to move; if opponent in check
    chess.undoMove();
    if(givesCheck) s += 80;

    return s;
  }

  _alphabeta(chess, depth, alpha, beta){
    if(this._timeUp()){ this.stop=true; return 0; }
    this.nodes++;

    const status = chess.gameStatus();
    if(status.over){
      if(status.reason==='checkmate'){
        // losing side to move is checkmated -> very negative
        return -100000 + (8-depth); // quicker mates better
      }
      return 0; // draw
    }
    if(depth<=0){
      let e = this.eval.evaluate(chess);
      if(this.noise){
        // noise that shrinks with game progress; makes easy blunder-ish but still legal
        const t = clamp((chess.fullmoveNumber-1)/20, 0, 1);
        const n = (1-t) * this.noise;
        e += Math.round((rand01()*2-1)*n);
      }
      return e;
    }

    // TT lookup
    const ttEntry = this.tt.get(chess.hash);
    if(ttEntry && ttEntry.depth >= depth){
      this.tt.hits++;
      if(ttEntry.flag===TT_FLAG.EXACT) return ttEntry.score;
      if(ttEntry.flag===TT_FLAG.LOWER) alpha = Math.max(alpha, ttEntry.score);
      else if(ttEntry.flag===TT_FLAG.UPPER) beta = Math.min(beta, ttEntry.score);
      if(alpha>=beta) return ttEntry.score;
    }

    let bestScore=-999999;
    let bestMove=null;

    let moves = chess.generateMoves({legal:true});
    // if TT has best move, place it first
    if(ttEntry && ttEntry.best){
      const uci = ttEntry.best;
      const ttMove = this._uciToMove(chess, uci);
      if(ttMove){
        moves = [ttMove, ...moves.filter(x => !(x.from===ttMove.from && x.to===ttMove.to && x.promo===ttMove.promo))];
      }
    }else{
      moves.sort((a,b)=> this._moveOrderScore(chess,b) - this._moveOrderScore(chess,a));
    }

    const alpha0=alpha;
    for(const m of moves){
      if(this.stop) break;
      chess.makeMove(m);
      const score = -this._alphabeta(chess, depth-1, -beta, -alpha);
      chess.undoMove();

      if(this.stop) break;

      if(score > bestScore){
        bestScore=score;
        bestMove=m;
      }
      if(score > alpha) alpha=score;
      if(alpha>=beta) break;
    }

    // store TT
    let flag = TT_FLAG.EXACT;
    if(bestScore <= alpha0) flag = TT_FLAG.UPPER;
    else if(bestScore >= beta) flag = TT_FLAG.LOWER;

    if(bestMove){
      this.tt.set(chess.hash, {depth, score:bestScore, flag, best:this._moveToUci(bestMove)});
    }else{
      this.tt.set(chess.hash, {depth, score:bestScore, flag});
    }

    return bestScore;
  }

  _moveToUci(m){
    const from = sqToAlg(m.from);
    const to = sqToAlg(m.to);
    let p='';
    if(m.flags & MOVE_FLAGS.PROMO){
      const t=typeOf(m.promo);
      p = ({2:'n',3:'b',4:'r',5:'q'})[t] || 'q';
    }
    return from+to+p;
  }

  _uciToMove(chess, uci){
    const from = chess.algToSq(uci.slice(0,2));
    const to = chess.algToSq(uci.slice(2,4));
    const promoChar = uci[4]||'';
    const legal = chess.generateMoves({legal:true});
    for(const m of legal){
      if(m.from===from && m.to===to){
        if(!promoChar && !(m.flags & MOVE_FLAGS.PROMO)) return m;
        if(promoChar && (m.flags & MOVE_FLAGS.PROMO)){
          const t = typeOf(m.promo);
          const c = ({2:'n',3:'b',4:'r',5:'q'})[t];
          if(c===promoChar) return m;
        }
      }
    }
    return null;
  }
}

// ======================== Renderer ==========================

class CanvasRenderer {
  constructor(canvas){
    this.canvas=canvas;
    this.ctx=canvas.getContext('2d', {alpha:true});
    this.dpr=1;
    this.size=900;
    this.flip=false;
    this.themeIndex=0;

    this.selectedSq=-1;
    this.legalTargets=[];
    this.lastMove=null;
    this.checkSq=-1;

    this.drag = {active:false, sq:-1, piece:0, x:0, y:0, ox:0, oy:0};

    this.anim = null; // {from,to,piece,start,dur}
    this.showHints=true;

    this._themes = [
      { name:"Royal", light:"#cdbfa7", dark:"#3b4766", edge:"#0b1020", glow:"#7c5cff" },
      { name:"Emerald", light:"#cfe6d6", dark:"#275a4f", edge:"#0b1020", glow:"#2dd4bf" },
      { name:"Sunset", light:"#f2d4bf", dark:"#6a2b3b", edge:"#0b1020", glow:"#ff8c3a" },
    ];

    this._resizeObserver = new ResizeObserver(()=>this.resizeToDisplay());
    this._resizeObserver.observe(canvas);
  }

  theme(){
    return this._themes[this.themeIndex % this._themes.length];
  }

  nextTheme(){
    this.themeIndex = (this.themeIndex+1) % this._themes.length;
  }

  setFlip(f){ this.flip=!!f; }

  resizeToDisplay(){
    const rect = this.canvas.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    const size = Math.floor(Math.min(rect.width, rect.height) * dpr);
    // keep square
    this.canvas.width = size;
    this.canvas.height = size;
    this.dpr=dpr;
    this.size=size;
  }

  sqFromXY(x,y){
    const s=this.size;
    const margin = this._margin();
    const boardSize = s - 2*margin;
    const cell = boardSize/8;
    const bx = x - margin;
    const by = y - margin;
    if(bx<0||by<0||bx>=boardSize||by>=boardSize) return -1;
    let f = Math.floor(bx/cell);
    let r = 7 - Math.floor(by/cell);
    if(this.flip){
      f = 7-f;
      r = 7-r;
    }
    return frToSq(f,r);
  }

  xyFromSq(sq){
    const s=this.size;
    const margin=this._margin();
    const boardSize = s - 2*margin;
    const cell = boardSize/8;
    let f=sqToFile(sq), r=sqToRank(sq);
    if(this.flip){ f=7-f; r=7-r; }
    const x = margin + f*cell + cell/2;
    const y = margin + (7-r)*cell + cell/2;
    return {x,y,cell};
  }

  _margin(){
    // comfortable outer edge for premium look
    return Math.max(18*this.dpr, this.size*0.03);
  }

  draw(chess){
    const ctx=this.ctx;
    const s=this.size;
    ctx.clearRect(0,0,s,s);

    // Ambient background layer
    this._drawAmbient(ctx);

    // Board
    const margin=this._margin();
    const boardSize = s - 2*margin;
    const cell = boardSize/8;

    // board shadow
    ctx.save();
    ctx.shadowColor="rgba(0,0,0,.55)";
    ctx.shadowBlur=28*this.dpr;
    ctx.shadowOffsetY=18*this.dpr;
    this._roundRect(ctx, margin, margin, boardSize, boardSize, 18*this.dpr);
    ctx.fillStyle="rgba(0,0,0,.32)";
    ctx.fill();
    ctx.restore();

    // inner board plate
    this._roundRect(ctx, margin, margin, boardSize, boardSize, 16*this.dpr);
    const plateGrad = ctx.createLinearGradient(margin, margin, margin+boardSize, margin+boardSize);
    plateGrad.addColorStop(0,"rgba(255,255,255,.06)");
    plateGrad.addColorStop(1,"rgba(0,0,0,.18)");
    ctx.fillStyle = plateGrad;
    ctx.fill();

    // squares
    const th=this.theme();
    for(let r=0;r<8;r++){
      for(let f=0;f<8;f++){
        const sq = frToSq(f,r);
        let ff=f, rr=r;
        if(this.flip){ ff=7-f; rr=7-r; }
        const x = margin + ff*cell;
        const y = margin + (7-rr)*cell;

        const dark = ((f+r)&1)===1;
        const base = dark ? th.dark : th.light;

        // subtle gradients for 3D feel
        const g = ctx.createLinearGradient(x,y,x+cell,y+cell);
        if(dark){
          g.addColorStop(0, this._shade(base, -10));
          g.addColorStop(1, this._shade(base, 10));
        }else{
          g.addColorStop(0, this._shade(base, 14));
          g.addColorStop(1, this._shade(base, -10));
        }
        ctx.fillStyle=g;
        ctx.fillRect(x,y,cell,cell);

        // vignette per square (very subtle)
        const vg = ctx.createRadialGradient(x+cell*0.25,y+cell*0.2,cell*0.1, x+cell*0.5,y+cell*0.55, cell*0.75);
        vg.addColorStop(0,"rgba(255,255,255,.05)");
        vg.addColorStop(1,"rgba(0,0,0,.10)");
        ctx.fillStyle=vg;
        ctx.fillRect(x,y,cell,cell);
      }
    }

    // overlays
    this._drawHighlights(ctx, cell);

    // pieces
    this._drawPieces(ctx, chess, cell);

    // border & gloss
    this._drawBoardFrame(ctx, margin, boardSize);
  }

  _drawAmbient(ctx){
    const s=this.size;
    const g1 = ctx.createRadialGradient(s*0.28,s*0.08, s*0.05, s*0.28,s*0.08, s*0.7);
    g1.addColorStop(0,"rgba(124,92,255,.14)");
    g1.addColorStop(1,"rgba(124,92,255,0)");
    ctx.fillStyle=g1; ctx.fillRect(0,0,s,s);

    const g2 = ctx.createRadialGradient(s*0.95,s*0.12, s*0.05, s*0.95,s*0.12, s*0.7);
    g2.addColorStop(0,"rgba(45,212,191,.12)");
    g2.addColorStop(1,"rgba(45,212,191,0)");
    ctx.fillStyle=g2; ctx.fillRect(0,0,s,s);
  }

  _drawBoardFrame(ctx, margin, boardSize){
    ctx.save();
    // border
    const borderGrad = ctx.createLinearGradient(margin,margin,margin+boardSize,margin+boardSize);
    borderGrad.addColorStop(0,"rgba(255,255,255,.14)");
    borderGrad.addColorStop(1,"rgba(255,255,255,.03)");
    ctx.strokeStyle=borderGrad;
    ctx.lineWidth=2*this.dpr;
    this._roundRect(ctx, margin+1*this.dpr, margin+1*this.dpr, boardSize-2*this.dpr, boardSize-2*this.dpr, 16*this.dpr);
    ctx.stroke();

    // gloss
    const gloss = ctx.createLinearGradient(margin,margin,margin,margin+boardSize);
    gloss.addColorStop(0,"rgba(255,255,255,.08)");
    gloss.addColorStop(.35,"rgba(255,255,255,.02)");
    gloss.addColorStop(1,"rgba(255,255,255,0)");
    ctx.globalCompositeOperation="screen";
    ctx.fillStyle=gloss;
    this._roundRect(ctx, margin+2*this.dpr, margin+2*this.dpr, boardSize-4*this.dpr, boardSize-4*this.dpr, 14*this.dpr);
    ctx.fill();
    ctx.restore();
  }

  _drawHighlights(ctx, cell){
    const th=this.theme();
    // last move
    if(this.lastMove){
      for(const sq of [this.lastMove.from, this.lastMove.to]){
        const {x,y,cell:cc} = this.xyFromSq(sq);
        const px=x-cc/2, py=y-cc/2;
        ctx.save();
        const g=ctx.createLinearGradient(px,py,px+cc,py+cc);
        g.addColorStop(0,"rgba(255,255,255,.08)");
        g.addColorStop(1,"rgba(255,255,255,.02)");
        ctx.fillStyle=g;
        ctx.fillRect(px,py,cc,cc);
        ctx.restore();
      }
    }

    // selected square glow
    if(this.selectedSq>=0){
      const {x,y,cell:cc} = this.xyFromSq(this.selectedSq);
      const px=x-cc/2, py=y-cc/2;
      ctx.save();
      ctx.strokeStyle = "rgba(124,92,255,.55)";
      ctx.lineWidth = 3*this.dpr;
      ctx.shadowColor = "rgba(124,92,255,.45)";
      ctx.shadowBlur = 16*this.dpr;
      ctx.strokeRect(px+2*this.dpr, py+2*this.dpr, cc-4*this.dpr, cc-4*this.dpr);
      ctx.restore();

      // legal targets dots/rings
      for(const t of this.legalTargets){
        const {x:tx,y:ty,cell:tc} = this.xyFromSq(t.to);
        const isCap = t.captured!==EMPTY || (t.flags & MOVE_FLAGS.EP);
        ctx.save();
        if(isCap){
          ctx.strokeStyle="rgba(255,255,255,.40)";
          ctx.lineWidth=3*this.dpr;
          ctx.globalAlpha=0.9;
          ctx.beginPath();
          ctx.arc(tx,ty, tc*0.33, 0, Math.PI*2);
          ctx.stroke();
        }else{
          ctx.fillStyle="rgba(255,255,255,.28)";
          ctx.beginPath();
          ctx.arc(tx,ty, tc*0.12, 0, Math.PI*2);
          ctx.fill();
        }
        ctx.restore();
      }
    }

    // check indicator around king
    if(this.checkSq>=0){
      const {x,y,cell:cc} = this.xyFromSq(this.checkSq);
      const px=x-cc/2, py=y-cc/2;
      ctx.save();
      ctx.strokeStyle = "rgba(255,77,109,.75)";
      ctx.lineWidth = 4*this.dpr;
      ctx.shadowColor = "rgba(255,77,109,.55)";
      ctx.shadowBlur = 20*this.dpr;
      ctx.strokeRect(px+3*this.dpr, py+3*this.dpr, cc-6*this.dpr, cc-6*this.dpr);
      ctx.restore();
    }
  }

  _drawPieces(ctx, chess, cell){
    // animation: if anim active, draw moving piece separately
    const moving = this.anim && (nowMs()-this.anim.start) < this.anim.dur;
    const movingSqFrom = moving ? this.anim.from : -1;
    const movingSqTo = moving ? this.anim.to : -1;

    // draw all pieces except moving one (source and destination should be empty/ignored)
    for(let sq=0;sq<64;sq++){
      const p=chess.board[sq];
      if(p===EMPTY) continue;
      if(moving && sq===movingSqTo) continue;
      if(this.drag.active && sq===this.drag.sq) continue; // dragged piece drawn on top
      const {x,y} = this.xyFromSq(sq);
      this._drawPiece(ctx, p, x, y, cell);
    }

    // moving animation
    if(moving){
      const t = clamp((nowMs()-this.anim.start)/this.anim.dur, 0, 1);
      const ease = t<.5 ? 2*t*t : 1 - Math.pow(-2*t+2,2)/2;
      const a = this.xyFromSq(this.anim.from);
      const b = this.xyFromSq(this.anim.to);
      const x = lerp(a.x,b.x,ease);
      const y = lerp(a.y,b.y,ease);
      this._drawPiece(ctx, this.anim.piece, x, y, cell);
    }

    // drag
    if(this.drag.active){
      this._drawPiece(ctx, this.drag.piece, this.drag.x, this.drag.y, cell, true);
    }
  }

  _drawPiece(ctx, piece, cx, cy, cell, lifted=false){
    const isW = isWhite(piece);
    const type = typeOf(piece); // 1..6
    const scale = lifted?1.06:1.00;
    const r = cell*0.36*scale;

    // shadow
    ctx.save();
    ctx.translate(cx,cy);
    ctx.shadowColor="rgba(0,0,0,.55)";
    ctx.shadowBlur = (lifted?18:14)*this.dpr;
    ctx.shadowOffsetY = (lifted?10:8)*this.dpr;

    // base color
    const base = isW ? "#f3f6ff" : "#101425";
    const rim  = isW ? "rgba(0,0,0,.25)" : "rgba(255,255,255,.14)";

    // glossy gradient
    const g = ctx.createRadialGradient(-r*0.35,-r*0.55, r*0.15, 0,0, r*1.25);
    g.addColorStop(0, isW? "rgba(255,255,255,.95)" : "rgba(255,255,255,.22)");
    g.addColorStop(.35, isW? "rgba(255,255,255,.55)" : "rgba(255,255,255,.10)");
    g.addColorStop(1, isW? "rgba(180,190,255,.20)" : "rgba(0,0,0,.40)");

    // draw simplified premium silhouettes per piece
    ctx.fillStyle=base;
    ctx.strokeStyle=rim;
    ctx.lineWidth=2*this.dpr;

    const drawBase = ()=>{
      ctx.beginPath();
      ctx.ellipse(0, r*0.92, r*0.95, r*0.34, 0, 0, Math.PI*2);
      ctx.fillStyle = isW ? "rgba(0,0,0,.08)" : "rgba(255,255,255,.08)";
      ctx.fill();
      ctx.beginPath();
      ctx.ellipse(0, r*0.78, r*0.92, r*0.30, 0, 0, Math.PI*2);
      ctx.fillStyle = g; ctx.fill();
      ctx.stroke();
    };

    const drawStem = (w=0.55, h=1.10)=>{
      ctx.beginPath();
      ctx.roundRect(-r*w, -r*h*0.10, 2*r*w, r*h, r*0.28);
      ctx.fillStyle=g; ctx.fill();
      ctx.stroke();
    };

    const drawCrown = ()=>{
      ctx.beginPath();
      ctx.ellipse(0,-r*0.72, r*0.75, r*0.42, 0, 0, Math.PI*2);
      ctx.fillStyle=g; ctx.fill();
      ctx.stroke();
      // highlight
      ctx.save();
      ctx.globalCompositeOperation="screen";
      ctx.fillStyle = isW ? "rgba(255,255,255,.28)" : "rgba(255,255,255,.10)";
      ctx.beginPath();
      ctx.ellipse(-r*0.18, -r*0.86, r*0.42, r*0.22, -0.3, 0, Math.PI*2);
      ctx.fill();
      ctx.restore();
    };

    const drawBall = (y, rr)=>{
      ctx.beginPath();
      ctx.arc(0,y, rr, 0, Math.PI*2);
      ctx.fillStyle=g; ctx.fill();
      ctx.stroke();
    };

    const drawCross = ()=>{
      ctx.save();
      ctx.strokeStyle = isW? "rgba(0,0,0,.28)" : "rgba(255,255,255,.18)";
      ctx.lineWidth = 3*this.dpr;
      ctx.beginPath();
      ctx.moveTo(0, -r*1.18);
      ctx.lineTo(0, -r*0.85);
      ctx.moveTo(-r*0.14, -r*1.02);
      ctx.lineTo(r*0.14, -r*1.02);
      ctx.stroke();
      ctx.restore();
    };

    // body
    if(type===1){ // pawn
      drawBall(-r*0.55, r*0.42);
      drawStem(0.45, 0.9);
      drawBase();
    }else if(type===2){ // knight
      // horse-head abstract
      drawStem(0.55, 0.95);
      ctx.beginPath();
      ctx.moveTo(-r*0.55, -r*0.85);
      ctx.quadraticCurveTo(-r*0.25, -r*1.25, r*0.25, -r*1.05);
      ctx.quadraticCurveTo(r*0.55, -r*0.90, r*0.42, -r*0.55);
      ctx.quadraticCurveTo(r*0.35, -r*0.20, -r*0.05, -r*0.25);
      ctx.quadraticCurveTo(-r*0.35, -r*0.28, -r*0.40, -r*0.50);
      ctx.closePath();
      ctx.fillStyle=g; ctx.fill();
      ctx.stroke();
      // eye
      ctx.save();
      ctx.fillStyle = isW? "rgba(0,0,0,.28)" : "rgba(255,255,255,.20)";
      ctx.beginPath(); ctx.arc(r*0.16, -r*0.78, r*0.06, 0, Math.PI*2); ctx.fill();
      ctx.restore();
      drawBase();
    }else if(type===3){ // bishop
      drawStem(0.52, 1.05);
      drawCrown();
      // slash
      ctx.save();
      ctx.strokeStyle = isW? "rgba(0,0,0,.18)" : "rgba(255,255,255,.14)";
      ctx.lineWidth = 4*this.dpr;
      ctx.beginPath();
      ctx.moveTo(-r*0.22, -r*0.96);
      ctx.lineTo(r*0.16, -r*0.52);
      ctx.stroke();
      ctx.restore();
      drawBase();
    }else if(type===4){ // rook
      drawStem(0.62, 0.98);
      // battlements
      ctx.beginPath();
      ctx.roundRect(-r*0.72, -r*1.05, r*1.44, r*0.28, r*0.10);
      ctx.fillStyle=g; ctx.fill();
      ctx.stroke();
      for(let i=-2;i<=2;i++){
        ctx.beginPath();
        ctx.roundRect(i*r*0.25 - r*0.08, -r*1.16, r*0.16, r*0.16, r*0.06);
        ctx.fillStyle = isW? "rgba(0,0,0,.08)" : "rgba(255,255,255,.08)";
        ctx.fill();
      }
      drawBase();
    }else if(type===5){ // queen
      drawStem(0.62, 1.05);
      // crown points
      ctx.beginPath();
      ctx.moveTo(-r*0.70, -r*0.95);
      ctx.lineTo(-r*0.45, -r*1.20);
      ctx.lineTo(-r*0.15, -r*0.95);
      ctx.lineTo(0, -r*1.25);
      ctx.lineTo(r*0.15, -r*0.95);
      ctx.lineTo(r*0.45, -r*1.20);
      ctx.lineTo(r*0.70, -r*0.95);
      ctx.closePath();
      ctx.fillStyle=g; ctx.fill();
      ctx.stroke();
      drawBall(-r*0.80, r*0.12);
      drawBase();
    }else if(type===6){ // king
      drawStem(0.62, 1.05);
      drawCrown();
      drawCross();
      drawBase();
    }

    ctx.restore();
  }

  _roundRect(ctx,x,y,w,h,r){
    ctx.beginPath();
    const rr = Math.min(r, w/2, h/2);
    ctx.moveTo(x+rr,y);
    ctx.arcTo(x+w,y,x+w,y+h,rr);
    ctx.arcTo(x+w,y+h,x,y+h,rr);
    ctx.arcTo(x,y+h,x,y,rr);
    ctx.arcTo(x,y,x+w,y,rr);
    ctx.closePath();
  }

  _shade(hex, percent){
    // percent: -100..100
    const c = hex.replace('#','');
    const num = parseInt(c,16);
    const r = (num>>16)&255;
    const g = (num>>8)&255;
    const b = num&255;
    const t = percent<0 ? 0 : 255;
    const p = Math.abs(percent)/100;
    const rr = Math.round((t-r)*p + r);
    const gg = Math.round((t-g)*p + g);
    const bb = Math.round((t-b)*p + b);
    return `rgb(${rr},${gg},${bb})`;
  }
}

// =========================== UI =============================

class UIController {
  constructor(){
    this.canvas = document.getElementById('board');
    this.toastEl = document.getElementById('toast');
    this.movelistEl = document.getElementById('movelist');
    this.capWEl = document.getElementById('capWhite');
    this.capBEl = document.getElementById('capBlack');
    this.turnPill = document.getElementById('turnPill');
    this.gamePill = document.getElementById('gamePill');
    this.engineHint = document.getElementById('engineHint');

    this.difficultyLabel = document.getElementById('difficultyLabel');
    this.youLabel = document.getElementById('youLabel');
    this.aiLabel = document.getElementById('aiLabel');

    this.startModal = document.getElementById('startModal');
    this.promoModal = document.getElementById('promoModal');

    this.btnStart = document.getElementById('btnStart');
    this.btnNew = document.getElementById('btnNew');
    this.btnRestart = document.getElementById('btnRestart');
    this.btnUndo = document.getElementById('btnUndo');
    this.btnFlip = document.getElementById('btnFlip');
    this.btnTheme = document.getElementById('btnTheme');

    this.toggleSound = document.getElementById('toggleSound');
    this.toggleHints = document.getElementById('toggleHints');

    this._soundEnabled = true;
    this._hintsEnabled = true;

    this.chess = new Chess();
    this.engine = new Engine();
    this.renderer = new CanvasRenderer(this.canvas);

    this.config = {
      level: null,
      humanSide: null, // 'w' or 'b'
      ranked: false
    };

    this.state = {
      busy:false,
      gameOver:false,
      flipped:false,
      pendingPromotion:null, // {from,to,piece,captured,flags, choicesMoves[]}
      lastLegal:[],
      moveSAN:[], // SAN strings in sequence
      capturedW:[], // pieces captured from white
      capturedB:[], // pieces captured from black
    };

    this._initModal();
    this._initButtons();
    this._initInput();
    this._initToggles();
    this._tick();
    this._updateUI();
  }

  _initModal(){
    let chosenSide=null, chosenLevel=null;
    const sideBtns=[...this.startModal.querySelectorAll('[data-side]')];
    const levelBtns=[...this.startModal.querySelectorAll('[data-level]')];

    const updateStartEnabled=()=>{
      const ok = !!chosenSide && !!chosenLevel;
      this.btnStart.disabled = !ok;
      if(ok){
        this.config.humanSide=chosenSide;
        this.config.level=chosenLevel;
      }
    };

    sideBtns.forEach(btn=>{
      btn.addEventListener('click', ()=>{
        sideBtns.forEach(b=>b.classList.remove('active'));
        btn.classList.add('active');
        chosenSide=btn.dataset.side;
        updateStartEnabled();
      });
    });
    levelBtns.forEach(btn=>{
      btn.addEventListener('click', ()=>{
        levelBtns.forEach(b=>b.classList.remove('active'));
        btn.classList.add('active');
        chosenLevel=btn.dataset.level;
        updateStartEnabled();
      });
    });

    this.btnStart.addEventListener('click', ()=>{
      this.config.ranked = document.getElementById('optRanked').checked;
      this.startModal.style.display='none';
      this._startNewGame();
    });

    // Promotion buttons
    [...this.promoModal.querySelectorAll('.promoBtn')].forEach(btn=>{
      btn.addEventListener('click', ()=>{
        const p=btn.dataset.promo;
        this._resolvePromotion(p);
      });
    });
  }

  _initButtons(){
    this.btnNew.addEventListener('click', ()=>{
      this.startModal.style.display='flex';
    });
    this.btnRestart.addEventListener('click', ()=>{
      this._startNewGame(true);
    });
    this.btnUndo.addEventListener('click', ()=>{
      if(this.config.ranked){ this._toast("Undo is disabled in Ranked mode."); return; }
      if(this.state.busy || this.state.gameOver) return;
      // undo one full ply (human move) + AI move if exists
      const undone1 = this.chess.undoMove();
      if(!undone1) return;
      const undone2 = this.chess.undoMove();
      // fix repetition counts already handled
      this.renderer.lastMove = this.chess.history.length ? this.chess.history[this.chess.history.length-1].move : null;
      this._rebuildMoveListFromHistory();
      this._rebuildCapturedFromHistory();
      this._syncSelection(-1);
      this._updateUI();
      this._toast("Undid last move.");
    });
    this.btnFlip.addEventListener('click', ()=>{
      this.state.flipped = !this.state.flipped;
      this.renderer.setFlip(this.state.flipped);
      this._syncSelection(this.renderer.selectedSq); // keep selection mapping same (sq is absolute)
      this._toast(this.state.flipped? "Board flipped." : "Board normal.");
    });
    this.btnTheme.addEventListener('click', ()=>{
      this.renderer.nextTheme();
      this._toast("Theme: " + this.renderer.theme().name);
    });
  }

  _initToggles(){
    this.toggleSound.addEventListener('change', ()=>{
      this._soundEnabled = !!this.toggleSound.checked;
    });
    this.toggleHints.addEventListener('change', ()=>{
      this._hintsEnabled = !!this.toggleHints.checked;
      this.renderer.showHints = this._hintsEnabled;
      if(!this._hintsEnabled){
        this.renderer.legalTargets = [];
      }else{
        if(this.renderer.selectedSq>=0) this._refreshLegalTargets(this.renderer.selectedSq);
      }
    });
  }

  _initInput(){
    const c=this.canvas;
    const getXY = (ev)=>{
      const rect=c.getBoundingClientRect();
      const x=(ev.clientX-rect.left)*(c.width/rect.width);
      const y=(ev.clientY-rect.top)*(c.height/rect.height);
      return {x,y};
    };

    const onDown = (ev)=>{
      if(this.state.busy || this.state.gameOver) return;
      if(this.state.pendingPromotion) return;

      c.setPointerCapture(ev.pointerId);
      const {x,y}=getXY(ev);
      const sq=this.renderer.sqFromXY(x,y);
      if(sq<0) return;

      const piece=this.chess.board[sq];
      const side=this.chess.sideToMove;
      const humanSide=this.config.humanSide;

      // only allow interaction if it's human's turn
      if(side!==humanSide) return;

      if(piece!==EMPTY && colorOf(piece)===side){
        this.renderer.drag.active=true;
        this.renderer.drag.sq=sq;
        this.renderer.drag.piece=piece;
        this.renderer.drag.x=x;
        this.renderer.drag.y=y;
        this.renderer.drag.ox=x;
        this.renderer.drag.oy=y;
        this._syncSelection(sq);
        this._refreshLegalTargets(sq);
      }else{
        // tap empty or opponent: treat as attempt move if selection exists
        if(this.renderer.selectedSq>=0){
          this._tryMoveTo(sq);
        }else{
          this._toast("Select a piece first.");
        }
      }
    };

    const onMove = (ev)=>{
      const {x,y}=getXY(ev);
      if(this.renderer.drag.active){
        this.renderer.drag.x=x; this.renderer.drag.y=y;
      }else{
        // hover effect not essential; could be added later
      }
    };

    const onUp = (ev)=>{
      if(this.renderer.drag.active){
        const {x,y}=getXY(ev);
        const fromSq=this.renderer.drag.sq;
        const toSq=this.renderer.sqFromXY(x,y);
        this.renderer.drag.active=false;
        if(toSq>=0){
          // if drop on same square, keep selection
          if(toSq===fromSq){
            this._syncSelection(fromSq);
            this._refreshLegalTargets(fromSq);
          }else{
            this._tryMoveTo(toSq);
          }
        }
      }else{
        // click-to-select on pointer up for non-drag taps
        const {x,y}=getXY(ev);
        const sq=this.renderer.sqFromXY(x,y);
        if(sq<0) return;
        this._onTapSquare(sq);
      }
    };

    c.addEventListener('pointerdown', onDown);
    c.addEventListener('pointermove', onMove);
    c.addEventListener('pointerup', onUp);
    c.addEventListener('pointercancel', ()=>{ this.renderer.drag.active=false; });
  }

  _onTapSquare(sq){
    if(this.state.busy || this.state.gameOver) return;
    if(this.state.pendingPromotion) return;

    const side=this.chess.sideToMove;
    if(side!==this.config.humanSide) return;

    const piece=this.chess.board[sq];
    if(piece!==EMPTY && colorOf(piece)===side){
      // select
      this._syncSelection(sq);
      this._refreshLegalTargets(sq);
      this._play('select');
    }else{
      // attempt move
      if(this.renderer.selectedSq>=0) this._tryMoveTo(sq);
    }
  }

  _refreshLegalTargets(fromSq){
    if(!this._hintsEnabled){
      this.renderer.legalTargets=[];
      return;
    }
    const legal=this.chess.generateMoves({legal:true});
    this.state.lastLegal=legal;
    this.renderer.legalTargets = legal.filter(m=>m.from===fromSq);
  }

  _syncSelection(sq){
    this.renderer.selectedSq = sq;
    if(sq<0){
      this.renderer.legalTargets=[];
    }
  }

  _tryMoveTo(toSq){
    const fromSq=this.renderer.selectedSq;
    if(fromSq<0) return;

    const legal = (this.state.lastLegal && this.state.lastLegal.length)
      ? this.state.lastLegal
      : this.chess.generateMoves({legal:true});

    const candidates = legal.filter(m=>m.from===fromSq && m.to===toSq);

    if(!candidates.length){
      // maybe selecting another own piece
      const p=this.chess.board[toSq];
      if(p!==EMPTY && colorOf(p)===this.chess.sideToMove){
        this._syncSelection(toSq);
        this._refreshLegalTargets(toSq);
        this._play('select');
        return;
      }
      this._toast("Illegal move.");
      this._play('error');
      return;
    }

    // promotion choice if needed and multiple candidates
    const promoMoves = candidates.filter(m=>m.flags & MOVE_FLAGS.PROMO);
    if(promoMoves.length){
      this.state.pendingPromotion = {from:fromSq, to:toSq, moves:promoMoves};
      this.promoModal.style.display='flex';
      return;
    }

    // otherwise pick first
    this._makeHumanMove(candidates[0]);
  }

  _resolvePromotion(choiceChar){
    const pending=this.state.pendingPromotion;
    if(!pending) return;
    // map choice to move with corresponding promo piece type
    const want = ({'q':5,'r':4,'b':3,'n':2})[choiceChar] || 5;
    const m = pending.moves.find(mm=>typeOf(mm.promo)===want) || pending.moves[0];
    this.state.pendingPromotion=null;
    this.promoModal.style.display='none';
    this._makeHumanMove(m);
  }

  async _makeHumanMove(m){
    if(this.state.busy || this.state.gameOver) return;

    // SAN before making move (SAN depends on current position)
    const san = this.chess.moveToSAN(m);

    // animate
    this._animateMove(m);
    this.chess.makeMove(m);
    m.san = san;
    this._recordMove(m);

    this._syncSelection(-1);
    this._updateUI();

    this._playMoveSound(m);

    // check end
    const status=this.chess.gameStatus();
    if(status.over){
      this.state.gameOver=true;
      this._updateUI();
      this._toast("Game over: " + status.reason + " ("+status.result+")");
      return;
    }

    // AI turn
    await this._aiTurn();
  }

  _animateMove(m){
    this.renderer.anim = {from:m.from, to:m.to, piece:m.piece, start:nowMs(), dur:190};
    this.renderer.lastMove = {from:m.from, to:m.to};
  }

  _recordMove(m){
    // rebuild captured from history is easier but we keep incremental:
    if(m.flags & MOVE_FLAGS.CAPTURE){
      const cap = (m.flags & MOVE_FLAGS.EP) ? (this.chess.sideToMove==='w'?BP:WP) : m.captured;
      if(isWhite(cap)) this.state.capturedW.push(cap);
      else if(isBlack(cap)) this.state.capturedB.push(cap);
    }
    // move list
    this.state.moveSAN.push(m.san);
    this._renderMoveList();
    this._renderCaptured();
  }

  _rebuildMoveListFromHistory(){
    this.state.moveSAN=[];
    // rebuild SAN by replaying from start using temp chess
    const tmp = new Chess();
    tmp.loadFEN("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    for(const h of this.chess.history){
      const m = h.move;
      const legal = tmp.generateMoves({legal:true});
      // find same move
      const found = legal.find(x=>x.from===m.from && x.to===m.to && x.promo===m.promo && x.flags===m.flags) || legal.find(x=>x.from===m.from && x.to===m.to && x.promo===m.promo);
      if(found){
        found.san = tmp.moveToSAN(found);
        this.state.moveSAN.push(found.san);
        tmp.makeMove(found);
      }else{
        // fallback UCI-like
        this.state.moveSAN.push(sqToAlg(m.from)+sqToAlg(m.to));
        tmp.makeMove(m);
      }
    }
    this._renderMoveList();
  }

  _rebuildCapturedFromHistory(){
    this.state.capturedW=[];
    this.state.capturedB=[];
    for(const h of this.chess.history){
      const m=h.move;
      if(m.flags & MOVE_FLAGS.CAPTURE){
        const cap = (m.flags & MOVE_FLAGS.EP) ? (colorOf(m.piece)==='w'?BP:WP) : m.captured;
        if(isWhite(cap)) this.state.capturedW.push(cap);
        else if(isBlack(cap)) this.state.capturedB.push(cap);
      }
    }
    this._renderCaptured();
  }

  _renderMoveList(){
    const san = this.state.moveSAN;
    let html='';
    for(let i=0;i<san.length;i+=2){
      const moveNo = (i/2)+1;
      const w = san[i] || '';
      const b = san[i+1] || '';
      html += `<div class="moveRow">
        <div class="moveNo">${moveNo}.</div>
        <div class="moveSan">${this._escape(w)}</div>
        <div class="moveSan ${b?'':'muted'}">${this._escape(b||'…')}</div>
      </div>`;
    }
    this.movelistEl.innerHTML = html;
    // auto scroll to bottom
    this.movelistEl.scrollTop = this.movelistEl.scrollHeight;
  }

  _escape(s){
    return String(s).replace(/[&<>"']/g, (c)=>({ '&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;' }[c]));
  }

  _renderCaptured(){
    const mapChar = (p)=>{
      const t=typeOf(p);
      return ({1:'♟',2:'♞',3:'♝',4:'♜',5:'♛',6:'♚'})[t] || '?';
    };
    this.capWhite = this.state.capturedW;
    this.capBlack = this.state.capturedB;
    this.capWEl.innerHTML = this.state.capturedW.map(p=>`<div class="capPiece">${mapChar(p)}</div>`).join('');
    this.capBEl.innerHTML = this.state.capturedB.map(p=>`<div class="capPiece">${mapChar(p)}</div>`).join('');
  }

  _playMoveSound(m){
    if(!this._soundEnabled) return;
    const isCap = (m.flags & MOVE_FLAGS.CAPTURE) || (m.flags & MOVE_FLAGS.EP);
    this._play(isCap?'capture':'move');
  }

  _play(kind){
    if(!this._soundEnabled) return;
    // tiny procedural audio (no assets)
    const ctx = UIController._audioCtx || (UIController._audioCtx = new (window.AudioContext||window.webkitAudioContext)());
    const t0 = ctx.currentTime;
    const o = ctx.createOscillator();
    const g = ctx.createGain();
    o.connect(g); g.connect(ctx.destination);
    const base = (kind==='move'? 520 : kind==='capture'? 320 : kind==='select'? 740 : 200);
    o.type = (kind==='error'?'sawtooth':'triangle');
    o.frequency.setValueAtTime(base, t0);
    o.frequency.exponentialRampToValueAtTime(base*0.85, t0+0.09);
    g.gain.setValueAtTime(0.0001, t0);
    g.gain.exponentialRampToValueAtTime(0.12, t0+0.01);
    g.gain.exponentialRampToValueAtTime(0.0001, t0+0.12);
    o.start(t0);
    o.stop(t0+0.13);
  }

  _toast(msg){
    this.toastEl.textContent=msg;
    this.toastEl.classList.add('show');
    clearTimeout(this._toastTimer);
    this._toastTimer=setTimeout(()=>this.toastEl.classList.remove('show'), 1400);
  }

  _startNewGame(restart=false){
    this.engine.setDifficulty(this.config.level || 'medium');
    this.difficultyLabel.textContent = (this.config.level||'medium').toUpperCase();
    this.youLabel.textContent = (this.config.humanSide==='w'?'White':'Black');
    this.aiLabel.textContent = (this.config.humanSide==='w'?'Black':'White');

    this.state.gameOver=false;
    this.state.busy=false;
    this.state.pendingPromotion=null;
    this.state.moveSAN=[];
    this.state.capturedW=[];
    this.state.capturedB=[];
    this.renderer.anim=null;
    this.renderer.lastMove=null;
    this._syncSelection(-1);

    this.chess.loadFEN("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    this._renderMoveList();
    this._renderCaptured();

    // auto flip if user chooses black (but still allow flip button)
    this.state.flipped = (this.config.humanSide==='b');
    this.renderer.setFlip(this.state.flipped);

    this._updateUI();
    this._toast(restart? "Restarted." : "New game started.");

    // if human is black, AI plays first
    if(this.chess.sideToMove !== this.config.humanSide){
      this._aiTurn();
    }
  }

  async _aiTurn(){
    if(this.state.gameOver) return;
    this.state.busy=true;
    this._syncSelection(-1);
    this.renderer.legalTargets=[];
    this._updateUI();

    const thinkSide = this.chess.sideToMove;
    this.engineHint.textContent = "AI thinking…";

    const move = await this.engine.think(this.chess, (info)=>{
      const s = info.book
        ? "Book move"
        : `Depth ${info.depth} • Nodes ${info.nodes.toLocaleString()} • TT ${info.ttHits.toLocaleString()} • Score ${this._fmtScore(info.score)}`;
      this.engineHint.textContent = s;
    });

    if(!move){
      this.state.busy=false;
      this.engineHint.textContent = "AI idle";
      this._updateUI();
      return;
    }

    // SAN before move
    const san = this.chess.moveToSAN(move);

    // animate (use moved piece from position)
    this._animateMove(move);
    this.chess.makeMove(move);
    move.san=san;
    this._recordMove(move);

    this._playMoveSound(move);

    this.state.busy=false;
    this.engineHint.textContent = "AI idle";

    const status=this.chess.gameStatus();
    if(status.over){
      this.state.gameOver=true;
      this._updateUI();
      this._toast("Game over: " + status.reason + " ("+status.result+")");
      return;
    }

    this._updateUI();
  }

  _fmtScore(score){
    // near mate scores
    if(Math.abs(score) > 90000){
      const m = Math.round((100000 - Math.abs(score))/2);
      return (score>0? "+M":"-M") + m;
    }
    const pawn = (score/100).toFixed(2);
    return (score>=0?"+":"") + pawn;
  }

  _updateUI(){
    const stm = this.chess.sideToMove;
    const status = this.chess.gameStatus();
    // check square
    if(status.inCheck){
      this.renderer.checkSq = this.chess.kingSquare(stm);
    }else{
      this.renderer.checkSq = -1;
    }

    // pills
    const turnText = (stm==='w' ? "White to move" : "Black to move");
    this.turnPill.textContent = turnText;

    if(status.over){
      this.gamePill.textContent = `Game over: ${status.reason} (${status.result})`;
      this.gamePill.style.borderColor = "rgba(255,255,255,.20)";
    }else if(status.inCheck){
      this.gamePill.textContent = "Check";
      this.gamePill.style.borderColor = "rgba(255,77,109,.45)";
    }else{
      this.gamePill.textContent = this.state.busy ? "AI thinking…" : "In progress";
      this.gamePill.style.borderColor = "rgba(255,255,255,.12)";
    }

    // Undo disabled in ranked
    this.btnUndo.disabled = this.config.ranked || this.state.busy || this.state.gameOver || this.chess.history.length===0;
    this.btnRestart.disabled = this.state.busy;
    this.btnFlip.disabled = this.state.busy;
    this.btnTheme.disabled = this.state.busy;
  }

  _tick(){
    // render loop
    this.renderer.draw(this.chess);
    requestAnimationFrame(()=>this._tick());
  }
}

// Boot
new UIController();
