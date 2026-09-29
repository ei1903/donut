(()=>{
'use strict';
const N_VALUES=[1,2,3,2,4],M_VALUES=[1,2,4,3,5];
const stages=N_VALUES.map((n,i)=>({n,m:M_VALUES[i]}));
// Face order: upper left, lower left, upper right, lower right.
// Each piece follows the original ring clockwise; the last one wraps past 12 o'clock.
stages.at(-1).initialPieces=[
 {who:0,start:1,end:5},   // yellow x3, red x1
 {who:2,start:5,end:9},   // red x3, green x1
 {who:3,start:9,end:13},  // green x3, blue x1
 {who:1,start:13,end:21}  // blue x3, purple x4, yellow x1
];
function minimumCuts(n,m){if(n===1)return 0;if(m===1)return n;if(n===2)return m+(m%2);return m*(n-1)}
function minimumCutsWithInitialPieces({n,m,initialPieces}){
 const total=n*m,full=(1<<n)-1,stateCount=n*n*(1<<n),boundaries=new Set(initialPieces.map(piece=>piece.end%total));
 let minimum=Infinity;
 for(let firstBoard=0;firstBoard<n;firstBoard++)for(let firstInitial=0;firstInitial<n;firstInitial++){
  let costs=Array(stateCount).fill(Infinity);
  costs[((firstBoard*n+firstInitial)<<n)|((1<<firstBoard)|(1<<firstInitial))]=0;
  for(let cell=1;cell<total;cell++){
   const next=Array(stateCount).fill(Infinity);
   for(let state=0;state<stateCount;state++){
    const oldCost=costs[state];if(!Number.isFinite(oldCost))continue;
    let seen=state&full;if(cell%n===0){if(seen!==full)continue;seen=0}
    const previousInitial=(state>>n)%n,previousBoard=Math.floor((state>>n)/n);
    for(let board=0;board<n;board++)for(let initial=0;initial<n;initial++){
     const mask=seen|(1<<board)|(1<<initial),key=((board*n+initial)<<n)|mask;
     const cost=oldCost+(previousBoard!==board)+(!boundaries.has(cell)&&previousInitial!==initial);
     if(cost<next[key])next[key]=cost;
    }
   }
   costs=next;
  }
  for(let state=0;state<stateCount;state++)if((state&full)===full){
   const previousInitial=(state>>n)%n,previousBoard=Math.floor((state>>n)/n);
   minimum=Math.min(minimum,costs[state]+(previousBoard!==firstBoard)+(!boundaries.has(0)&&previousInitial!==firstInitial));
  }
 }
 return minimum;
}
const S=stages.reduce((sum,stage)=>sum+(stage.initialPieces?minimumCutsWithInitialPieces(stage):minimumCuts(stage.n,stage.m)),0);
const colors=['#f4ce82','#e99da9','#9ac58e','#89bce0','#b6a3df','#edb079','#75cfc5','#d991bc','#bfc980','#95a7ea'];
const HIT_IMAGE='assets/images/impact.png';
const SHARE_TEXT='「Donuts」をクリアしました！\nhttps://ei1903.github.io/donuts/';
const NS='http://www.w3.org/2000/svg',TWO=Math.PI*2,CY=300,OUT=217,IN=105;
const FACE_LAYOUTS={1:[{x:100,y:300}],2:[{x:88,y:300},{x:812,y:300}],3:[{x:88,y:185},{x:88,y:415},{x:812,y:300}],4:[{x:88,y:185},{x:88,y:415},{x:812,y:185},{x:812,y:415}]};
function faces(){return FACE_LAYOUTS[stages[level].n]}
function donutX(){return stages[level].n===1?555:450}
function cellCount(){const {n,m}=stages[level];return n*m}
function slotCount(){const {n,m}=stages[level];return n===1&&m===1?0:n*m}
const $=id=>document.getElementById(id);
let level=0,cuts=[],pieces=[],nextPieceId=0,totalCuts=0,eaten=new Map(),history=[],returning=new Set(),returnTimers=new Set(),hover=null,hoverFace=null,down=null,drag=null,locked=false,finished=false,knifeBroken=false,breaking=false,shakingFace=null,timer=null,shakeTimer=null;
function make(tag,attrs,parent){const e=document.createElementNS(NS,tag);for(const [k,v] of Object.entries(attrs))e.setAttribute(k,v);parent.appendChild(e);return e}
function point(a,r){return [donutX()+Math.sin(a)*r,CY-Math.cos(a)*r]}
function angle(cell){return cell*TWO/cellCount()}
function sector(a,b,parent,fill){if(b-a>=TWO-1e-8){sector(a,a+Math.PI,parent,fill);sector(a+Math.PI,b,parent,fill);return}
 const p=point(a,OUT),q=point(b,OUT),u=point(b,IN),v=point(a,IN),large=b-a>Math.PI?1:0;
 make('path',{d:`M ${p[0]} ${p[1]} A ${OUT} ${OUT} 0 ${large} 1 ${q[0]} ${q[1]} L ${u[0]} ${u[1]} A ${IN} ${IN} 0 ${large} 0 ${v[0]} ${v[1]} Z`,fill},parent)}
function currentPieces(){return pieces}
function interiorSlot(piece,slot){let v=slot;if(v<=piece.start)v+=cellCount();return v<piece.end?v:null}
function canCut(slot){if(knifeBroken||breaking||slot===null||slot<0||slot>=slotCount()||cuts.includes(slot))return false;return currentPieces().some(piece=>!eaten.has(piece.id)&&!returning.has(piece.id)&&((piece.end-piece.start===cellCount()&&!piece.slit)||interiorSlot(piece,slot)!==null))}
function syncKnifeCursor(){let available=false;for(let i=0;i<slotCount();i++)if(canCut(i)){available=true;break}$('board').classList.toggle('no-cuts',!available)}
function drawPiece(piece,split,parent=$('pieces')){const group=make('g',{},parent);if(drag?.id===piece.id)group.setAttribute('transform',`translate(${drag.dx} ${drag.dy})`);
 for(let cell=piece.start;cell<piece.end;){const n=stages[level].n,stop=Math.min(piece.end,n*(Math.floor(cell/n)+1));sector(angle(cell),angle(stop),group,colors[Math.floor(cell/n)%stages[level].m]);cell=stop}
 const boundaries=piece.slit?[piece.start]:piece.end-piece.start<cellCount()?[piece.start,piece.end]:[];
 for(const boundary of boundaries){const p=point(angle(boundary),IN),q=point(angle(boundary),OUT);make('line',{x1:p[0],y1:p[1],x2:q[0],y2:q[1],stroke:'#1e2430','stroke-width':4},group)}return group}
function portionCounts(){const {n,m}=stages[level],total=cellCount(),counts=Array.from({length:n},()=>Array(m).fill(0));for(const piece of currentPieces()){const who=eaten.get(piece.id);if(who===undefined)continue;for(let cell=piece.start;cell<piece.end;cell++)counts[who][Math.floor((cell%total)/n)]++}return counts}
function faceSatisfied(who,counts=portionCounts()){const m=stages[level].m,row=counts[who];return row.filter(amount=>amount>0).length===m&&row.every(amount=>amount>=1)}
function drawPeople(){const g=$('people'),counts=portionCounts();g.replaceChildren();faces().forEach((face,i)=>{const happy=faceSatisfied(i,counts),person=make('g',{'class':'face-target'+(shakingFace===i?' face-shake':'')},g),active=hoverFace===i,stroke=happy?'#9bd9b6':'#ff792f';make('circle',{cx:face.x,cy:face.y,r:83,fill:'transparent','class':'face-hit'},person);make('circle',{cx:face.x,cy:face.y,r:active?64:58,fill:active?(happy?'#9bd9b625':'#ff792f25'):'none',stroke,'stroke-width':3},person);for(const offset of [-19,19])make('circle',{cx:face.x+offset,cy:face.y-13,r:5.5,fill:stroke},person);make('path',{d:happy?`M ${face.x-31} ${face.y+22} Q ${face.x} ${face.y+47} ${face.x+31} ${face.y+22}`:`M ${face.x-31} ${face.y+47} Q ${face.x} ${face.y+22} ${face.x+31} ${face.y+47}`,fill:'none',stroke,'stroke-width':3,'stroke-linecap':'round'},person)})}
function draw(){const pieces=$('pieces'),marks=$('marks');pieces.replaceChildren();marks.replaceChildren();drawPeople();const n=slotCount(),s=[...cuts].sort((a,b)=>a-b);
 const available=currentPieces().filter(p=>!eaten.has(p.id)&&!returning.has(p.id));for(const p of available)if(drag?.id!==p.id)drawPiece(p,s.length>=1);for(const p of available)if(drag?.id===p.id)drawPiece(p,s.length>=1);
 for(let i=0;i<n;i++){const a=angle(i),p=point(a,233),q=point(a,249),r=point(a,262),used=cuts.includes(i);make('line',{x1:p[0],y1:p[1],x2:q[0],y2:q[1],stroke:used?'#f4d28b':'#77818e','stroke-width':used?4:2,'stroke-linecap':'round'},marks);make('circle',{cx:r[0],cy:r[1],r:used?4:3,fill:used?'#f4d28b':'#77818e'},marks)}syncKnifeCursor();drawGuide()}
function drawGuide(){const g=$('guide');g.replaceChildren();if(locked||drag||!canCut(hover))return;const p=point(angle(hover),251),q=point(angle(hover),262);make('line',{x1:donutX(),y1:CY,x2:p[0],y2:p[1],stroke:'#fff8e5','stroke-width':3,'stroke-dasharray':'6 7','stroke-linecap':'round'},g);make('circle',{cx:q[0],cy:q[1],r:9,fill:'#f4d28b',stroke:'#1e2430','stroke-width':3},g)}
function local(e){const box=$('board').getBoundingClientRect();return{x:(e.clientX-box.left)*900/box.width,y:(e.clientY-box.top)*600/box.height}}
function nearest(p){const x=p.x-donutX(),y=p.y-CY,r=Math.hypot(x,y),n=slotCount();if(n===0||r<28||r>290)return null;const a=(Math.atan2(x,-y)+TWO)%TWO;return Math.round(a/TWO*n)%n}
function pieceAt(p){const x=p.x-donutX(),y=p.y-CY,r=Math.hypot(x,y);if(r<IN-10||r>OUT+17)return null;const n=cellCount(),a=(Math.atan2(x,-y)+TWO)%TWO,cell=a/TWO*n;return currentPieces().find(piece=>{let v=cell;if(v<piece.start)v+=n;return v>=piece.start&&v<piece.end&&!eaten.has(piece.id)&&!returning.has(piece.id)})||null}
function faceAt(p){return faces().findIndex(face=>Math.hypot(p.x-face.x,p.y-face.y)<83)}
function impact(faceIndex,hit){clearTimeout(shakeTimer);shakingFace=faceIndex;drawPeople();shakeTimer=setTimeout(()=>{shakingFace=null;drawPeople()},400);make('image',{href:HIT_IMAGE,x:hit.x-32,y:hit.y-30,width:64,height:60,'class':'damage-image'},$('effects'))}
function samePattern(a,b){if(a.end-a.start!==b.end-b.start)return false;const {n}=stages[level],total=cellCount();for(let i=0;i<a.end-a.start;i++)if(Math.floor(((a.start+i)%total)/n)!==Math.floor(((b.start+i)%total)/n))return false;return true}
function freeAt(start,length){const total=cellCount();for(const piece of currentPieces())if(!eaten.has(piece.id)||returning.has(piece.id)){for(let a=start;a<start+length;a++)for(let b=piece.start;b<piece.end;b++)if(a%total===b%total)return false}return true}
function vomit(faceIndex,hit){
 const last=history.findLastIndex(item=>item.who===faceIndex&&eaten.has(item.id));
 if(last<0){impact(faceIndex,hit);return}
 const source=currentPieces().find(p=>p.id===history[last].id);
 const length=source?.end-source?.start;
 let target=null;
 if(source&&!returning.has(source.id))for(let start=0;start<cellCount();start++){const candidate={start,end:start+length};if(samePattern(source,candidate)&&freeAt(start,length)){target=candidate;break}}
 if(!target){impact(faceIndex,hit);return}
 history.splice(last,1);eaten.delete(source.id);source.start=target.start;source.end=target.end;
 returning.add(source.id);
 if(locked&&finished){clearTimeout(timer);locked=false;finished=false;$('board').classList.remove('win');$('congrats').hidden=true;$('celebration').replaceChildren()}
 draw();
 const mouth=faces()[faceIndex],origin=point(angle((target.start+target.end)/2),(IN+OUT)/2);
 const ghost=drawPiece(source,cuts.length>=1,$('effects'));ghost.setAttribute('class','returning-piece');ghost.setAttribute('style',`--dx:${mouth.x-origin[0]}px;--dy:${mouth.y+32-origin[1]}px;--cx:${origin[0]}px;--cy:${origin[1]}px`);
 impact(faceIndex,hit);
 const returnTimer=setTimeout(()=>{returnTimers.delete(returnTimer);ghost.remove();returning.delete(source.id);draw()},520);returnTimers.add(returnTimer)
}
function burstFaces(){const layer=$('celebration');layer.replaceChildren();for(const face of faces()){make('circle',{cx:face.x,cy:face.y,r:61,fill:'none',stroke:'#9bd9b6','stroke-width':3,'class':'clear-ring'},layer);const burst=make('g',{'class':'clear-burst'},layer);for(let i=0;i<10;i++){const a=i*TWO/10,dx=Math.cos(a),dy=Math.sin(a);make('line',{x1:face.x+dx*67,y1:face.y+dy*67,x2:face.x+dx*81,y2:face.y+dy*81,stroke:i%2?'#f4ce82':'#9bd9b6','stroke-width':3.5,'stroke-linecap':'round'},burst)}}}
function check(){if(locked)return;const counts=portionCounts();if(!counts.every((_,i)=>faceSatisfied(i,counts)))return;locked=true;finished=true;hover=null;hoverFace=null;$('board').classList.remove('face-hover');$('board').classList.add('win','locked');drawGuide();drawPeople();burstFaces();if(level<stages.length-1)timer=setTimeout(()=>start(level+1),1200);else timer=setTimeout(()=>$('congrats').hidden=false,1000)}
function cut(slot){if(locked||!canCut(slot))return;const piece=currentPieces().find(p=>!eaten.has(p.id)&&!returning.has(p.id)&&((p.end-p.start===cellCount()&&!p.slit)||interiorSlot(p,slot)!==null));if(piece.end-piece.start===cellCount()&&!piece.slit){piece.start=slot;piece.end=slot+cellCount();piece.slit=true}else{let boundary=slot;if(boundary<=piece.start)boundary+=cellCount();pieces.push({id:nextPieceId++,start:boundary,end:piece.end,slit:false});piece.end=boundary;piece.slit=false}cuts.push(slot);totalCuts++;hover=null;draw();if(totalCuts===S){knifeBroken=true;breaking=true;$('board').classList.add('broken');syncKnifeCursor();$('knife-break').hidden=false;timer=setTimeout(()=>{breaking=false;$('knife-break').hidden=true;drawGuide()},1050)}}
function start(n){clearTimeout(timer);clearTimeout(shakeTimer);for(const t of returnTimers)clearTimeout(t);returnTimers.clear();returning.clear();shakingFace=null;if(n===0){totalCuts=0;knifeBroken=S===0}breaking=false;level=n;cuts=[];nextPieceId=0;pieces=[{id:nextPieceId++,start:0,end:cellCount(),slit:false}];eaten=new Map();history=[];for(const initial of stages[level].initialPieces??[]){const piece={id:nextPieceId++,start:initial.start,end:initial.end,slit:false};pieces.push(piece);eaten.set(piece.id,initial.who);history.push({id:piece.id,who:initial.who})}hover=null;hoverFace=null;down=null;drag=null;locked=false;finished=false;$('effects').replaceChildren();$('celebration').replaceChildren();$('knife-break').hidden=true;$('congrats').hidden=true;$('board').classList.remove('win','dragging','locked','face-hover');if(!knifeBroken)$('board').classList.remove('broken');$('stage-number').textContent=String(n+1).padStart(2,'0');$('stage-total').textContent='/ '+String(stages.length).padStart(2,'0');draw()}
const board=$('board');board.addEventListener('pointermove',e=>{if(locked)return;const p=local(e);board.classList.toggle('face-hover',faceAt(p)>=0);if(down){const dx=p.x-down.p.x,dy=p.y-down.p.y;if(!drag&&down.piece&&Math.hypot(dx,dy)>10){drag={id:down.piece.id,dx,dy};board.classList.add('dragging')}if(drag){drag.dx=dx;drag.dy=dy;const face=faceAt(p);hoverFace=face<0?null:face;draw()}return}const next=nearest(p);if(next!==hover){hover=next;drawGuide()}});
board.addEventListener('pointerleave',()=>{if(!down){board.classList.remove('face-hover');hover=null;drawGuide()}});
board.addEventListener('pointerdown',e=>{if(e.button!==0||breaking||locked)return;const p=local(e),face=faceAt(p);board.classList.toggle('face-hover',face>=0);if(face>=0){e.preventDefault();board.setPointerCapture?.(e.pointerId);down={p,face};return}const piece=pieceAt(p);if(piece||canCut(nearest(p))){e.preventDefault();board.setPointerCapture?.(e.pointerId);down={p,piece}}});
board.addEventListener('pointerup',e=>{if(e.button!==0||!down)return;e.preventDefault();const p=local(e);board.classList.toggle('face-hover',faceAt(p)>=0);if(down.face!==undefined){const face=down.face;down=null;if(faceAt(p)===face)vomit(face,p);return}if(drag){const face=faceAt(p);if(face>=0){eaten.set(drag.id,face);history.push({id:drag.id,who:face});hoverFace=null;drag=null;down=null;board.classList.remove('dragging');draw();check();return}}else{const slot=nearest(p);down=null;cut(slot);return}down=null;drag=null;hoverFace=null;board.classList.remove('dragging');draw()});
board.addEventListener('pointercancel',()=>{down=null;drag=null;hoverFace=null;board.classList.remove('dragging');draw()});
board.addEventListener('contextmenu',e=>e.preventDefault());
board.addEventListener('keydown',e=>{if(locked||breaking)return;const n=slotCount();if(n===0)return;if(e.key==='ArrowRight'||e.key==='ArrowLeft'){e.preventDefault();hover=hover===null?0:(hover+(e.key==='ArrowRight'?1:n-1))%n;drawGuide()}else if(e.key==='Enter'||e.key===' '){e.preventDefault();cut(hover)}});
const shareIntent=new URL('https://x.com/intent/tweet');shareIntent.searchParams.set('text',SHARE_TEXT);$('share-x').href=shareIntent.toString();
$('reset').addEventListener('click',()=>start(0));start(0);
})();
