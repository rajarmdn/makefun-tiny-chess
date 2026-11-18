import os,json,urllib.request

W,B=0,1
P,N,BI,R,Q,K=1,2,3,4,5,6
CAP,EP,CASTLE,P2=1,2,4,8
MATE=30000
VALMG=[0,82,337,365,477,1025,0]
VALEG=[0,94,281,297,512,936,0]
PH=[0,0,1,1,2,4,0]
PMG=[];PEG=[]
for t in range(6):
 a=[];b=[]
 for r in range(8):
  for f in range(8):
   c=7-abs(3-2*f)-abs(3-2*(7-r))
   a.append((r*10 if t==0 else 0)+c*(2 if t in (1,2) else 1)-(r==0 and t==5)*35)
   b.append((r*7 if t==0 else 0)+c-(r<2 and t==5)*20)
 PMG.append(a);PEG.append(b)

_seed=0x9E3779B97F4A7C15
def rnd():
 global _seed
 _seed^=(_seed<<7)&((1<<64)-1);_seed^=_seed>>9;_seed^=(_seed<<8)&((1<<64)-1)
 return _seed&((1<<64)-1)
Z=[[rnd() for _ in range(128)] for _ in range(12)]
ZS=rnd();ZC=[rnd() for _ in range(16)];ZE=[rnd() for _ in range(128)]
RM=[15]*128
for s in range(128):
 if not s&8: RM[s]=15
RM[0]&=14;RM[7]&=13;RM[112]&=11;RM[119]&=7
DIRN=(33,31,18,14,-14,-18,-31,-33)
DIRB=(17,15,-17,-15);DIRR=(16,-16,1,-1);DIRK=DIRB+DIRR
PROM={'q':Q,'r':R,'b':BI,'n':N}
PC=' pnbrqk'

def sq(x): return (ord(x[0])-97)+16*(ord(x[1])-49)
def us(s): return chr(97+(s&7))+str((s>>4)+1)
def ix(s): return (s&7)+8*(s>>4)
def sideof(p): return 0 if p>0 else 1
def on(s): return 0<=s<128 and not s&8
def zi(p,s): return (abs(p)-1)+(6 if p<0 else 0)

def uci(m):
 a=us(m[0])+us(m[1])
 return a+(PC[m[2]] if m[2] else '')
def pm(s):
 try:
  a,b=sq(s[:2]),sq(s[2:4]);return a,b,PROM.get(s[4],0) if len(s)>4 else 0
 except: return -1,-1,0

class Pos:
 def __init__(self,fen):
  self.b=[0]*128;self.st=W;self.cr=0;self.ep=-1;self.half=0;self.full=1
  self.mg=self.eg=self.ph=0;self.bc=[0,0];self.key=0
  a=fen.split(); ranks=a[0].split('/')
  for rr,row in enumerate(ranks):
   f=0
   for c in row:
    if c.isdigit(): f+=int(c)
    else:
     p=PC.index(c.lower())
     if c.isupper(): p=-p if False else p
     else: p=-p
     s=(7-rr)*16+f;self.b[s]=p;self.add(p,s);f+=1
  self.st=0 if a[1]=='w' else 1
  for c in a[2] if len(a)>2 else '-':
   self.cr|={'K':1,'Q':2,'k':4,'q':8}.get(c,0)
  self.ep=-1 if len(a)<4 or a[3]=='-' else sq(a[3])
  self.half=int(a[4]) if len(a)>4 else 0;self.full=int(a[5]) if len(a)>5 else 1
  self.key=self.hashkey()
 def hashkey(self):
  k=ZC[self.cr]
  for s in range(128):
   if not s&8 and self.b[s]: k^=Z[6 if self.b[s]<0 else 0][s] if False else Z[(abs(self.b[s])-1)+(6 if self.b[s]<0 else 0)][s]
  if self.st:k^=ZS
  if self.ep>=0:k^=ZE[self.ep]
  return k
 def add(self,p,s):
  if not p:return
  c=0 if p>0 else 1;t=abs(p);z=ix(s^(112 if c else 0));sg=1 if c==0 else -1
  self.mg+=sg*(VALMG[t]+PMG[t-1][z]);self.eg+=sg*(VALEG[t]+PEG[t-1][z]);self.ph+=PH[t]
  if t==BI:
   if self.bc[c]==1:self.mg+=sg*35;self.eg+=sg*50
   self.bc[c]+=1
 def rem(self,p,s):
  if not p:return
  c=0 if p>0 else 1;t=abs(p);z=ix(s^(112 if c else 0));sg=1 if c==0 else -1
  if t==BI:
   if self.bc[c]==2:self.mg-=sg*35;self.eg-=sg*50
   self.bc[c]-=1
  self.mg-=sg*(VALMG[t]+PMG[t-1][z]);self.eg-=sg*(VALEG[t]+PEG[t-1][z]);self.ph-=PH[t]
 def king(self,c):
  p=K if c==0 else -K
  for s in range(128):
   if not s&8 and self.b[s]==p:return s
  return -1
 def attacked(self,s,by):
  pp=1 if by==0 else -1
  for d in (-15,-17) if by==0 else (15,17):
   t=s+d
   if on(t) and self.b[t]==pp:return True
  for d in DIRN:
   t=s+d
   if on(t) and self.b[t]==(N if by==0 else -N):return True
  kp=K if by==0 else -K
  for d in DIRK:
   t=s+d
   if on(t) and self.b[t]==kp:return True
  for ds,types in ((DIRB,(BI,Q)),(DIRR,(R,Q))):
   for d in ds:
    t=s+d
    while on(t):
     p=self.b[t]
     if p:
      if p==(types[0] if by==0 else -types[0]) or p==(types[1] if by==0 else -types[1]):return True
      break
     t+=d
  return False
 def pseudo(self):
  out=[];c=self.st;sg=1 if c==0 else -1
  for s in range(128):
   if not on(s):continue
   p=self.b[s]
   if not p or (p>0)!=(c==0):continue
   t=abs(p)
   if t==P:
    d=16*sg;n=s+d
    if on(n) and not self.b[n]:
     if n>>4 in (0,7):
      out += [(s,n,x,0) for x in (Q,R,BI,N)]
     else:
      out.append((s,n,0,0))
      if s>>4==(1 if c==0 else 6) and not self.b[s+2*d]:out.append((s,s+2*d,0,P2))
    for d in (15,17) if c==0 else (-15,-17):
     n=s+d
     if not on(n):continue
     if self.b[n] and (self.b[n]>0)!=(c==0):
      if n>>4 in (0,7):out += [(s,n,x,CAP) for x in (Q,R,BI,N)]
      else:out.append((s,n,0,CAP))
     if n==self.ep:out.append((s,n,0,CAP|EP))
   elif t==N:
    for d in DIRN:
     n=s+d
     if not on(n):continue
     q=self.b[n]
     if not q or (q>0)!=(c==0):out.append((s,n,0,CAP if q else 0))
   elif t in (BI,R,Q):
    ds=DIRB if t==BI else DIRR if t==R else DIRK
    for d in ds:
     n=s+d
     while on(n):
      q=self.b[n]
      if not q:out.append((s,n,0,0))
      else:
       if (q>0)!=(c==0):out.append((s,n,0,CAP))
       break
      n+=d
   else:
    for d in DIRK:
     n=s+d
     if not on(n):continue
     q=self.b[n]
     if not q or (q>0)!=(c==0):out.append((s,n,0,CAP if q else 0))
    if c==0 and s==4 or c==1 and s==116:
     if not self.attacked(s,1-c):
      if self.cr&(1 if c==0 else 4) and self.b[s+1]==0 and self.b[s+2]==0 and self.b[s+3]==(R if c==0 else -R) and not self.attacked(s+1,1-c) and not self.attacked(s+2,1-c):out.append((s,s+2,0,CASTLE))
      if self.cr&(2 if c==0 else 8) and self.b[s-1]==0 and self.b[s-2]==0 and self.b[s-3]==0 and self.b[s-4]==(R if c==0 else -R) and not self.attacked(s-1,1-c) and not self.attacked(s-2,1-c):out.append((s,s-2,0,CASTLE))
  return out
 def make(self,m):
  fr,to,pr,fl=m; p=self.b[fr];cap=to
  if fl&EP:cap=to-16 if p>0 else to+16
  ch={fr:self.b[fr],to:self.b[to],cap:self.b[cap]}
  if fl&CASTLE:
   rf=fr+3 if to>fr else fr-4;rt=fr+1 if to>fr else fr-1;ch[rf]=self.b[rf];ch[rt]=self.b[rt]
  u=(ch,self.st,self.cr,self.ep,self.half,self.full,self.mg,self.eg,self.ph,self.bc[:],self.key)
  key=self.key^ZC[self.cr]^(ZE[self.ep] if self.ep>=0 else 0)^Z[zi(p,fr)][fr]
  self.rem(p,fr);self.b[fr]=0
  captured=self.b[cap] if cap!=fr else 0
  if captured:self.rem(captured,cap);self.b[cap]=0;key^=Z[zi(captured,cap)][cap]
  if cap!=to:self.b[to]=0
  np=(pr if pr else abs(p))*(1 if p>0 else -1);self.add(np,to);self.b[to]=np;key^=Z[zi(np,to)][to]
  if fl&CASTLE:
   rf=fr+3 if to>fr else fr-4;rt=fr+1 if to>fr else fr-1;rp=self.b[rf];self.rem(rp,rf);self.b[rf]=0;self.add(rp,rt);self.b[rt]=rp;key^=Z[zi(rp,rf)][rf]^Z[zi(rp,rt)][rt]
  self.cr &= RM[fr]&RM[to];self.ep=-1
  if fl&P2:self.ep=(fr+to)//2
  self.half=0 if abs(p)==P or captured else self.half+1
  if self.st:self.full+=1
  self.st^=1;self.key=key^ZC[self.cr]^(ZE[self.ep] if self.ep>=0 else 0)^ZS;return u
 def unmake(self,u):
  ch,st,cr,ep,half,full,mg,eg,ph,bc,key=u
  for s,v in ch.items():self.b[s]=v
  self.st,self.cr,self.ep,self.half,self.full=u[1:6];self.mg,self.eg,self.ph=u[6:9];self.bc=bc;self.key=key
 def legal(self):
  out=[]
  for m in self.pseudo():
   u=self.make(m);ok=not self.attacked(self.king(self.st^1),self.st);self.unmake(u)
   if ok:out.append(m)
  return out
 def val(self):
  x=(self.mg*self.ph+self.eg*(24-min(24,self.ph)))//24
  return x if self.st==0 else -x
 def choose(self,server):
  ls=self.legal();mp={uci(m):m for m in ls};cand=[mp[x] for x in server if x in mp]
  if not cand:
   return server[0] if server else None
  S=Search(self);return uci(S.go(cand))

class Search:
 def __init__(self,p):
  self.p=p;self.n=0;self.limit=12000;self.tt={};self.kl=[None]*64;self.hist={};self.stop=False;self.best=None
 def tick(self):
  self.n+=1
  if self.n>=self.limit:raise StopIteration
 def keym(self,m):return (m[0],m[1],m[2])
 def order(self,ms,tt=None,ply=0):
  p=self.p
  def sc(m):
   fr,to,pr,fl=m;q=p.b[to] if not fl&EP else P
   z=(10000000 if tt and m==tt else 0)+(900000 if pr else 0)+(100000 if fl&CAP else 0)+abs(q)*20-(abs(p.b[fr]) if p.b[fr] else 0)
   if ply<64:
    if self.kl[ply]==m:z+=8000
    if self.kl[ply+1] == m:z+=7000
   z+=self.hist.get((p.st,fr,to),0)
   return -z
  return sorted(ms,key=sc)
 def q(self,a,b,ply):
  self.tick();p=self.p;chk=p.attacked(p.king(p.st),p.st^1)
  stand=-MATE+ply if chk else p.val()
  if not chk:
   if stand>=b:return stand
   if stand>a:a=stand
  ms=p.legal();ms=[m for m in ms if chk or (m[3]&CAP) or m[2]]
  for m in self.order(ms,ply=ply):
   u=p.make(m)
   try:v=-self.q(-b,-a,ply+1)
   finally:p.unmake(u)
   if v>=b:return v
   if v>a:a=v
  return a
 def nm(self,depth,a,b,ply,allow=True):
  self.tick();p=self.p;chk=p.attacked(p.king(p.st),p.st^1);e=p.val()
  ent=self.tt.get(p.key)
  if ent and ent[0]>=depth:
   d,v,bo,m=ent
   if bo==0:return v
   if bo==1 and v>=b:return v
   if bo==2 and v<=a:return v
  if depth<=0:return self.q(a,b,ply)
  if not chk and depth<=2 and e-90*depth>=b:return e
  if allow and depth>=3 and not chk and any(abs(x)>=N for x in p.b):
   old=(p.st,p.ep,p.key);p.key^=ZE[p.ep] if p.ep>=0 else 0;p.ep=-1;p.st^=1;p.key^=ZS
   try:v=-self.nm(depth-1-(1 if depth>5 else 0),-b,-b+1,ply+1,False)
   finally:p.st,p.ep,p.key=old
   if v>=b:return v
  ms=p.legal()
  if not ms:return -MATE+ply if chk else 0
  olda=a;best=None;first=True
  tm=ent[3] if ent else None
  for m in self.order(ms,tm,ply):
   u=p.make(m)
   try:
    if first:v=-self.nm(depth-1,-b,-a,ply+1,True)
    else:
     v=-self.nm(depth-1,-a-1,-a,ply+1,True)
     if a<v<b:v=-self.nm(depth-1,-b,-a,ply+1,True)
   finally:p.unmake(u)
   first=False
   if v>a:a=v;best=m
   if a>=b:
    if not (m[3]&CAP):
     self.kl[ply+1]=self.kl[ply];self.kl[ply]=m;self.hist[(p.st,m[0],m[1])]=self.hist.get((p.st,m[0],m[1]),0)+depth*depth
    break
  bo=0 if a>olda and a<b else 1 if a>=b else 2
  if len(self.tt)>50000:self.tt.clear()
  self.tt[p.key]=(depth,a,bo,best)
  return a
 def go(self,ms):
  self.best=ms[0];last=self.best
  for d in range(1,20):
   a=-MATE;bb=MATE;bm=None
   try:
    for m in self.order(ms,self.best,0):
     u=self.p.make(m)
     try:v=-self.nm(d-1,-bb,-a,1,True)
     finally:self.p.unmake(u)
     if v>a:a=v;bm=m
    if bm:last=bm;self.best=bm
   except StopIteration:break
  return last

class StopIteration(Exception):pass

def post(path,data):
 url=os.environ.get('MAKEFUN_ENV_URL','').rstrip('/')+path
 req=urllib.request.Request(url,json.dumps(data).encode(),{'Content-Type':'application/json'},method='POST')
 with urllib.request.urlopen(req,timeout=20) as r:return json.loads(r.read())

def main():
 r=post('/game',{})
 while r.get('status')!='done':
  if r.get('status')=='your_move':
   game=r.get('game');legal=r.get('legal_moves') or []
   if legal:
    try:mv=Pos(r['fen']).choose(legal)
    except Exception:mv=legal[0]
    if mv not in legal:mv=legal[0]
    r=post('/move',{'game':game,'move':mv})
   else:
    r=post('/resign',{'game':game})
  else:r=post('/game',{})
if __name__=='__main__':
 try:main()
 except Exception:
  pass
