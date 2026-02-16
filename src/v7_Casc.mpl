# By Marcelo 02.03.22
# changes to v7: sanitation to CascPhase and better track of the parents, added procedure WE8dec
# List of procedures to implement the Cascade algorithm
# Remarks about the Data Structures: for each (X,n) geometry, we will have:
# n+1 Gen files labelled Genk.mpl for k = 0..n. Each Gen0.mpl is initialized by hand and Gen(k+1).mpl is constructed in Phase k and consists of spaces of cod k.
# n+1 Std files labelled Stdk.mpl for k = 0..(n-1) and Std.mpl. Each Stdk.mpl is constructed in Phase k and consists of spaces of cod k. Std is the final database.
###########
### Std ### 
###########
# An array with 8 columns and rows as many as there are relevant standard position spaces crossed in Casc  
# Col 1: L0    = a pole space in dominant position
# Col 2: c0    = centre of L0
# Col 3: [g]   = a list of Weyl group elements such that L = gL0 appears in the contour-shift (so the same L0 may occur with different g's) -- one for each segment of column 4
# Col 4: Seg   = A list of segments [pini,pfin] in L0 (so it counts multiplicities); segments will be vizualized as 2D-Arrays -- for the cod 0 spaces, it will be only a list of points
# Col 5: pord  = pole order of the crossing
# Col 6: SUB   = tag on L0: 'true' if L=gL0 is residual or a subspace of a residual space in Std[k-1]  and 'false' otherwise 
# Col 7: [J,g] = standard Levi Data of L0
# Col 8: Perp  = set of roots perpendicular to L0
# Col 9: PAR   = list [r1,..,rp] of roots where the segment [pini,pfin] is constant on the (non-constant) root hyperplane rj of L0 and [] otherwise.
# Col10: [L]   = the corresponding list of spaces L = wL0 occuring in Casc
###########
### Gen ### 
###########
# An array with 8 columns and as many rows as there are spaces met in phase k 
# Col 1: L      = pole space crossed
# Col 2: pL     = point of crossing
# Col 3: cL     = centre of L
# Col 4: pord   = pole order of the crossing
# Col 5: num    = numerators of F.G|L after cancellations
# Col 6: den    = denominators of F.G|L after cancellations
# Col 7: inddat = [J,g,rl], indicates from which induction space this space is from

add2Gen := proc(G::Array,L::set,inddat::list, dat::Array,Y::symbol,m::integer,K::list,X::symbol,n::integer)::Array; 
description "adds the data 'dat' -- the output of PolesCrossed -- to the Gen array observing the ordering of the Casc algorithm";
# the input inddat is the list [J,g,rl] that indicates how L appears in Casc.
	uses ListTools, ArrayTools;
	local new, i, r, todo, ret, nline, CP, pP, aux, pPerp, orb;
	if ( evalb(nops(Dimensions(dat))=0) ) then
		return G;
	end if;
	new  := [seq(dat(i,1),i=1..RowDimension(dat))];
	todo := convert(new,set);
	ret  := G;
	while ( nops(todo)>0 ) do
		r          := Search(todo[1],new);
		nline      := Array(1..1,1..7);
		nline(1,1) := dat(r,1);
		nline(1,2) := dat(r,2);
		nline(1,3) := Coord2WDD(CentL(dat(r,1),X,n),X,n);
		nline(1,4) := dat(r,4);
		nline(1,5) := dat(r,5);
		nline(1,6) := dat(r,6);	
		nline(1,7) := [inddat[1],inddat[2],[op(inddat[3]),dat(r,3)]]; 
		if ( evalb(nops(Dimensions(ret))=0) ) then # this line tests if the array ret is empty or not
			ret := nline;
		else
			ret := Concatenate(1,ret,nline);
		end if;
		pPerp := Perp2pRts(L,dat(r,2),Y,m,K,X,n);
		orb   := GenPerpOrb(dat(r,1),pPerp,X,n);
		todo  := todo minus orb;
	end do;
	return ret;
end proc; #add2Gen

AdmEqs := proc(H0::set,d::list,GR::set,Y::symbol,m::integer,Ky::list,X::symbol,n::integer)
description "Given a regular hull and d minimal for W', computes the equations for Den-Sigma and Den-Sigma' allowing for cancellations of numerators of the Sigma'-sum";
	uses ListTools;
	local R, Rp, j, k, aux, preDenSig, bux, cux, oaux, gH0, dgH0, DendH0, DendH0num, DendH0den, Rd, dCoc, dCocnum, dCocden, dNums, DenSig, DenSigp, ret1, ret2, p, q;
	R   := PoscoRoot(CartMatrix(X,n)):
	aux := YminXn(Y,m,Ky,X,n):
	Rp  := {seq(aux[j],j=1..nops(aux))}:
	# First compute the denominators of the Sigma-sum without "numerators cancellation"; this is preDenSigma
	aux       := NablEl(H0,H0,H0,X,n):
	bux       := Vector(nops(aux[1])):
	cux       := Vector(nops(aux[1])):
	for k from 1 to nops(aux[1]) do
		bux[k] := [SearchAll(aux[1][k],aux[2])];
		cux[k] := sort([seq(aux[3][bux[k][p]],p=1..nops(bux[k]))],output=permutation);
	end do:
	oaux      := [seq(seq(bux[q][cux[q][p]],p=1..nops(cux[q])),q=1..nops(aux[1]))]:
	preDenSig := [seq(aux[2][oaux[j]]+aux[3][oaux[j]],j=1..nops(oaux))];
	# Second, we compute the denominators in Den(dH0,1,Sigma')|_{dH0}; this is DendH0
	gH0       := stdWDD(H0,X,n);
	dgH0      := WDDWeyl(gH0,d,X,n);
	DendH0num := [seq(DotProduct(dgH0,convert(R[Rp[j]],list))+1,j=1..nops(Rp))];
	DendH0den := [seq(DotProduct(dgH0,convert(R[Rp[j]],list))  ,j=1..nops(Rp))];
	DendH0    := Canc([seq(parse(convert(DendH0num[j],string)),j=1..nops(DendH0num))],[seq(parse(convert(DendH0den[k],string)),k=1..nops(DendH0den))])[2];
	# Third, we compute the cocycle expression r(d\lamb)/r(\lamb) with \lamb in H0; this is dCoc
	Rd      := RwSpeed(d,X,n);
	dCocnum := [seq(DotProduct(convert(R[Rd[j]],list),gH0)+1,j=1..nops(Rd))];
	dCocden := [seq(DotProduct(convert(R[Rd[j]],list),gH0)  ,j=1..nops(Rd))];
	dCoc    := Canc([seq(parse(convert(dCocnum[j],string)),j=1..nops(dCocnum))],[seq(parse(convert(dCocden[k],string)),k=1..nops(dCocden))]);
	# Fourth, we compute the numerators of dCoc that survive cancellations versus the denominators in DendH0
	dNums := Canc([seq(parse(convert(dCoc[1][j],string)),j=1..nops(dCoc[1]))],[seq(parse(convert(DendH0[k],string)),k=1..nops(DendH0))])[1];
	# Fifth, we cancel the remaining numerators of dCoc with the denominators of the preDenSigma to get DenSig
	DenSig := Canc([seq(parse(convert(dNums[j],string)),j=1..nops(dNums))],[seq(parse(convert(preDenSig[k],string)),k=1..nops(preDenSig))])[2];
	# Sixth we compute the denominators of the Sigma'-sum -- since H0 is regular, this ammounts to the second column of the tilde-denoms procedure
	aux     := tDenoms(H0,d,GR,H0,Y,m,Ky,X,n);
	DenSigp := [seq( seq(aux[2][j][1] ,k=1..aux[2][j][2]) ,j=1..LinearAlgebra:-Dimension(aux[2]))];
	# Finally, we construct the output as a list of column Vectors, the 1st entry the Sigma and the second the Sigma' sum.
	ret1 := Vector(nops(DenSig)):
	for j from 1 to nops(DenSig) do
		ret1[j] := subs({seq(x[k]=y[k],k=1..n)},parse(convert(DenSig[j],string)));
	end do:
	ret2 := Vector(nops(DenSigp)):
	for j from 1 to nops(DenSigp) do
		ret2[j] := subs({seq(x[k]=y[k],k=1..n)},parse(convert(DenSigp[j],string)));
	end do:
	return [ret1,ret2];
end proc; # AdmEqs

add2Std := proc(S::Array,dat::list,X::symbol,n::integer)::Array;
description "adds the data 'dat' to the Std array observing the ordering of the Casc algorithm";
# The ordering in std is weakly increasing w.r.t. dimension (so MPS comes first); also, we group together rows with same L0 but different w.
	uses ArrayTools, ListTools;
	local newline, i, j, ret, Ls, r, pos;
	newline := Array(1..1,1..nops(dat));
	for i from 1 to nops(dat) do
		newline(1,i) := dat[i];
	end do;
	if ( evalb(nops(Dimensions(S))=0) ) then # Check if the array S im empty (initial state)
		return newline;
	else
		Ls := [seq(S(i,1),i=1..RowDimension(S))];	
		r  := [SearchAll(dat[1],Ls)];
		if ( evalb(nops(r)>0) and evalb(r[-1]<RowDimension(S)) ) then # Check if L0=dat[1] is already in Std; in this case include together with the other L0's (the entry w may change)
			pos := r[-1]; # This is the last position where L0=dat[1] is and we include the new entry in the end of the block equal to L0; if this is the last entry of S, insert in the end
			ret := Concatenate(1,S([seq(i,i=1..pos)],..),newline,S([seq(i,i=(pos+1)..RowDimension(S))],..));	
		else                  # if not, include L0=dat[1] in the end of Std Database
			ret := Concatenate(1,S,newline);
		end if;
	end if;
	return ret;
end proc; #add2Std

CancThreeL := proc(num::list,den::list)
description "receives two 3-lists of numerators and denominators and cancels their common factors";
# num = [num[1],num[2],num[3]] and den=[den[1],den[2],den[3]]
# 1. returns the cancelled expression, 2. returns the positions where the factors that remains after the cancelation are.
# Important: the input num, den may contain constant factors. We cancel the non constant linear expressions and remove the constant values.
	uses ListTools;
	local k, j, aux, Num, Den, NUM, DEN, ret, rDen, rNum, i, val, canc, Num1, Num2, Num3, rden, rnum, N;
	rden    := Array(1..3);                        # rden stores the entries of den that will remain
	rden[1] := [seq(i,i=1..nops(den[1]))];         
	rden[2] := [seq(i,i=1..nops(den[2]))];
	rden[3] := [seq(i,i=1..nops(den[3]))];
	rnum    := Array(1..3);                        # rnum stores the entries of num that will remain
	rnum[1] := [seq(i,i=1..nops(num[1]))];
	rnum[2] := [seq(i,i=1..nops(num[2]))];
	rnum[3] := [seq(i,i=1..nops(num[3]))];
	Num := num;
	Den := den;
	# The idea is to start with the full list and erase things depending if: 1. we find a constant entry and 2. we find a cancellation of factors
	for k from 1 to 3 do 					         # These lines specifies which are the non-constant entries 
		N   := nops(Num[k]);
        	aux := [seq(type(num[k][j],numeric),j=1..nops(num[k]))]; # This line finds the position of the constant numerators
		j   := 1:                                                # starts the loop
		while ( j<=N )  do                                       #
			if aux[j] then                                   #
				aux     := subsop(j=NULL,aux);           #
				Num[k]  := subsop(j=NULL,Num[k]);        # This line removes the constant entry of the linear factors
				rnum[k] := subsop(j=NULL,rnum[k]);       # This line remotes the positions
			else
				j := j+1;
			end if;
			N := nops(Num[k]);
		end do;
		N   := nops(Den[k]);
		aux := [seq(type(den[k][j],numeric),j=1..nops(den[k]))]; # This line finds the position of the constant denominators
		j   := 1:                                                # starts the loop
		while ( j<=N )  do                                       #
			if aux[j] then                                   #
				aux     := subsop(j=NULL,aux);           #
				Den[k]  := subsop(j=NULL,Den[k]);        # This line removes the constant entry of the linear factors
				rden[k] := subsop(j=NULL,rden[k]);       # This line remotes the positions
			else
				j := j+1;
			end if;
			N := nops(Den[k]);
		end do;
        end do;
	DEN  := [op(Den[1]),op(Den[2]),op(Den[3])]; # DEN = union of all Den[j]'s
	# if 1 <= val <= num[1], Den[1]+1 <= val <= Den[1]+Den[2], Den[1]+Den[2]+1 <= val <= Den[1]+Den[2]+Den[3].
	for k from 1 to 3 do                                                                  		   
		N := nops(Num[k]);
		i := 1; 
		while ( i<= N ) do                                                      	       	      # for each numerator, search for occurences in the denominator to cancel
			aux := [seq(type(simplify(Num[k][i]/DEN[j]),numeric),j=1..nops(DEN))];		      # cancellation means if Num[k][i]=Den[j] up to a constant factor 
			val := Search(true,aux);                                               		      # val is the first entry of DEN that is a constant times NUM[k][i]
			if ( val>0 ) then                                                      		      # means there is cancellation of this denominator Num[k][i]
				DEN     := subsop(val=NULL,DEN);                              		      # erase entry val from DEN 
				Num[k]  := subsop(i=NULL,Num[k]);                             		      # indicate with 'true' that the entry i of Num[k] was cancelled
				rnum[k] := subsop(i=NULL,rnum[k]);					      # indicate with 'true' that the entry i of rnum[k] was cancelled
				if ( evalb(val<=nops(Den[1])) ) then					      # depending on the interval val is, removes from k = 1, 2, or 3
					Den[1]   := subsop(val=NULL,Den[1]);				      # of Den[k] and rden[k]
					rden[1]  := subsop(val=NULL,rden[1]);				      #
				elif ( evalb(nops(Den[1])+1<=val and val<=nops(Den[1])+nops(Den[2])) ) then #
					Den[2]   := subsop((val-nops(Den[1]))=NULL,Den[2]);		      #
					rden[2]  := subsop((val-nops(Den[1]))=NULL,rden[2]);		      #
				else									      #
					Den[3]   := subsop((val-nops(Den[1])-nops(Den[2]))=NULL,Den[3]);      #
					rden[3]  := subsop((val-nops(Den[1])-nops(Den[2]))=NULL,rden[3]);     #
				end if;
			else    # 'else' means there was no cancellation
				i := i+1;
			end if;
			N := nops(Num[k]);
		end do;	
		# At this point, rnum (resp. rden), and Num (resp. Den) are the Numerators (resp.  Denominators) that are left: rnum is the positions and Num are the actual linear factors
	end do;
	ret    := Vector(2);
	ret[1] := [Num,Den];
	ret[2] := [rnum,rden];
	return ret;
end proc; # CancThreeL

CstAndPerp := proc(L::set,X::symbol,n::integer)::list;
description "returns a list with two entries: 1. set of cst roots on L and 2. set of roots that are orthogonal the set of constant roots of L";
	uses LinearAlgebra;
	local R, Rv, cst, B, j, ret, IP, k;
	R   := PoscoRoot(CartMatrix(X,n));
	Rv  := R.SimpcoRoot(X,n);
	cst := Cst(L,X,n);
	B   := Basis({seq(Rv[cst[j]],j=1..nops(cst))});
	ret := {};
	for j from 1 to RowDimension(R) do
		IP := [seq(evalb(DotProduct(B[k],Rv[j])=0),k=1..nops(B))];
		if ( evalb(ListTools:-Search(false,IP)=0) ) then
			ret := ret union {j};		
		end if;
	end do;
	return [cst,ret];
end proc; # CstAndPerp

DistWSL := proc(L::set,M::set,Y::symbol,m::integer,K::list,X::symbol,n::integer,S::set) 
description "returns a list [test,w]: test = 'true' means dist(L,W(S)M)=0, 'false' it is not and w = the W(S) element that minimizes the distance between W(S)M and L.";	
# the input S is the set of reflections in the Weyl group W(S); for W' S is convert(YminXn(Y,m,K,X,n),set)
	uses ListTools, LinearAlgebra;
	local cL, cM, dp, ret, R, i, j, dpc, aux, F, wM, neworb, oldorb, pos, ch, nline, s;
	cL  := CentL(L,X,n);
	cM  := CentL(M,X,n);
	dp  := DistWSPt(cL,cM,X,n,S);
	ret := Vector(2);
	if ( dp[1] ) then
		R      := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
		dpc    := [seq(LinearAlgebra:-DotProduct(cL,R[S[i]]),i=1..nops(S))];
		aux    := [SearchAll(0,dpc)];
		F      := {seq(S[aux[i]],i=1..nops(aux))};
		wM     := LWeyl(M,dp[2],X,n);
		oldorb := Matrix(); 
		neworb := Matrix([wM,[]]);
		while ( evalb(RowDimension(oldorb)<RowDimension(neworb)) ) do
			oldorb := neworb;
			aux    := <seq(Matrix([seq(RtReflL(oldorb(j,1),F[i],X,n),j=1..RowDimension(oldorb))]),i=1..nops(F))>;
			for i from 1 to nops(F) do
				for j from 1 to RowDimension(oldorb) do
					if ( not member(aux(i,j),neworb) ) then
						nline  := Matrix([aux(i,j),[F[i],op(oldorb(j,2))]]);
						neworb := <neworb,nline>;
					end if;
				end do;
			end do;
		end do;
		if ( member(L,neworb) ) then
			pos    := Search(L,[seq(neworb(i,1),i=1..RowDimension(neworb))]);
			ret[1] := true;
			s      := proc(g,i::integer) RtRefl(g,i,X,n) end proc;
			ch     := Coord2WDD(foldl(s,GenPt({seq(j,j=1..n)},X,n),seq(neworb(pos,2)[i],i=1..nops(neworb(pos,2)))),X,n);
			ret[2] := [op(WDDDomElem(ch,X,n)),op(dp[2])];
		else
			ret[1] := false;
			ret[2] := dp[2];
		end if;
	else
		ret := dp;
	end if;
	return ret;
end proc; # DistWSL

DistWSPt := proc(p::Vector,q::Vector,X::symbol,n::integer,S::set)
description "returns a list [test,w]: test = 'true' means dist(p,W(S)q)=0, 'false' it is not and w = the W(S) element s.t. p = w(q) if true (if false it minimizes the distance but do not mean much).";
	uses ListTools;
	local d, w,v, Ndis, key, rv, ds, MIN, pos, ret, s, ch, i, j;
	d   := LinearAlgebra:-DotProduct(p-q,p-q);
	w   := []:
	ret := Vector(2);
	if ( evalb(nops(S)=0) ) then
		ret[1] := evalb(d=0);
		ret[2] := w;
		return ret;
	end if; 
	v    := q:
	Ndis := d:
	key  := 1:
	while ( key>0 ) do
		rv  := [seq(RtRefl(v,S[i],X,n),i=1..nops(S))];
		ds  := [seq(LinearAlgebra:-DotProduct(p-rv[i],p-rv[i]),i=1..nops(S))];
		MIN := FindMinimalElement(ds);
		if ( evalb( MIN<Ndis ) ) then
			Ndis := MIN;
			pos  := Search(MIN,ds);
			w    := [op(S[pos]),op(w)];
			v    := rv[pos];
		else
			key := 0;
		end if;
	end do;
	if ( evalb(LinearAlgebra:-DotProduct(p-v,p-v)=0) ) then	
		ret[1] := true;
	else
		ret[1] := false;
	end if;
	s      := proc(g,i::integer) RtRefl(g,i,X,n) end proc;
	ch     := Coord2WDD(foldl(s,GenPt({seq(j,j=1..n)},X,n),seq(w[i],i=1..nops(w))),X,n);
	ret[2] := WDDDomElem(ch,X,n);
	return ret;
end proc; # DitsWSPt

DistpPts := proc(p::list,Pts::set,Perp::set,Y::symbol,m::integer,K::list,X::symbol,n::integer)
description "computes [f,q] with f in F inter W', q in Pts such that dist(f(p),Pts) = dist(f(p),q)). Here F=<Perp>";
# Given a point p in L, outside Pts, use the reflections in the set Perp' = Perp\cap R'
# to find an element f \in F\cap W' (here F \cap W' = <Perp'>) such that the distance
# of f(p) to Pts is minimal. Also give a point Q \in Pts such that dist(Q, f(p)) equals
# dist(Pts, f(p)).
	uses ListTools,LinearAlgebra;
	local P, PTS, Rp, F, ds, i, wP, DS, MIN;
	P   := WDD2Coord(p,X,n);
	PTS := [seq(WDD2Coord(Pts[i],X,n),i=1..nops(Pts))];
	Rp  := convert(YminXn(Y,m,K,X,n),set);
	F   := Perp intersect Rp;
	ds  := Vector(nops(PTS));
	for i from 1 to nops(PTS) do
		ds[i] := DistWSPt(PTS[i],P,X,n,F);
	end do;
	wP  := [seq(vWeyl(P,ds[i][2],X,n),i=1..Dimension(ds))];
	DS  := [seq(LinearAlgebra:-DotProduct(wP[i]-PTS[i],wP[i]-PTS[i]),i=1..nops(PTS))];
	MIN := [FindMinimalElement(DS,position)];
	return [ds[MIN[2]][2],Pts[MIN[2]]];
end proc; #DistpPts

GenPerpOrb := proc(M::set,Perp::set,X::symbol,n::integer)
description "Perp a set of coroots, M a pole space, construct the orbit of M unders the reflection group generated by Perp";
	local R, oldorb, neworb,  i, r, N;
	R      := PoscoRoot(CartMatrix(X,n));
	oldorb := {};
	neworb := {M};	
	while ( evalb(nops(neworb)>nops(oldorb)) ) do
		oldorb := neworb;
		for i from 1 to nops(oldorb) do	
			for r from 1 to nops(Perp) do
				N      := RtReflL(oldorb[i],Perp[r],X,n);
				neworb := neworb union {N};
			end do;
		end do;
	end do;
	return neworb;
end proc; # GenPerpOrb

InStdWp := proc(S::Array,L::set,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list; 
description "returns the row of Std containing (L0,g) for which L is W' conjugate to gL0. Returns [row,u] or []; if non-empty, ug(Std(row,1)) = L with u in W'";
	uses ListTools,ArrayTools;
	local ret, r, L1, N, test;
	if ( evalb(nops(Dimensions(S))=0) ) then
		return [];
	end if;
	# Update in v4: even if L is not in Std, there could be a W'-conjugate of L already in Std. We MUST check for that
	ret := [];
	N   := RowDimension(S);
	r   := 1;
	while ( evalb(r<=N) ) do
		L1   := S(r,10)[1];
		test := WpConjug(L,L1,Y,m,K,X,n);
		if ( test[1] ) then
			ret := [r,test[2]];
			r   := N+1;
		else
			r := r+1;
		end if;
	end do;
	return ret;
end proc; #InStdWp

Jg2L := proc(J::set,g::list,X::symbol,n::integer)::set;
description "returns the pole space L out of the nipotent orbit data";
	local R, K, j, k, G, x, L;
	R := PoscoRoot(CartMatrix(X,n));
	K := {seq(k,k=1..n)} minus J;
	G := Vector(n): 
	for j from 1 to nops(J) do 
		G[J[j]] := g[j]: 
	od; 
	for k from 1 to nops(K) do 
		G[K[k]] := x[k]: 
	od: 
	L := PoleSet(convert(G,list),R):
	return L;
end proc; # Jg2L;

Jgrl2LInd := proc(J::set,g::list,rl::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::set;
description "returns the pole space of (X,n) after inputing the inducing data (J,g) of (Y,m) and the list of roots crossed rl";
	local R, Inc, Lp, L, j, u;
	R   := PoscoRoot(CartMatrix(X,n));
	Inc := YminXn(Y,m,K,X,n);
	Lp  := Jg2L(J,g,Y,m);
	L   := PoleSet(Coord2WDD(GenPt({seq(Inc[Lp[j]],j=1..nops(Lp))} union {seq(rl[u],u=1..nops(rl))},X,n),X,n),R);
	return L;
end proc; # Jg2LInd

JumpsSucc := proc(RR::Matrix)::Vector; 
description "Computes the successor jump vector";
	uses LinearAlgebra;
	local jumps, i, aux, bux, j; 
	jumps := Vector(RowDimension(RR)); 
	for i from 1 to RowDimension(RR) - 1 do 
		if type(RR(i, 1), numeric) then 
			jumps[i] := 0; 
		else 
			if evalb(RR(i + 1, 1) - RR(i, 1) = 1) then 
				jumps[i] := nops(RR(i, 2)) - nops(RR(i + 1, 2)); 
			else 
				jumps[i] := nops(RR(i, 2)); 
			end if; 
		end if; 
	end do; 
	jumps[RowDimension(RR)] := nops(RR(RowDimension(RR), 2)); 
	return jumps; 
end proc; # JumpsSucc

JumpsPred := proc(RR::Matrix)::Vector; 
description "Computes the predecessor jump vector";
	uses LinearAlgebra;
	local k, jumps, i, aux, bux, j; 
	k := 1; 
	while type(RR(k, 1), numeric) do 
		k := k + 1; 
	end do; 
	jumps := Vector(RowDimension(RR)); 
	jumps[k] := nops(RR(k, 2)); 
	for i from k + 1 to RowDimension(RR) do 
		if evalb(RR(i, 1) - RR(i - 1, 1) = 1) then 
			jumps[i] := nops(RR(i, 2)) - nops(RR(i - 1, 2)); 
		else 
			jumps[i] := nops(RR(i, 2)); 
		end if; 
	end do; 
	return jumps; 
end proc; # JumpsPred

JumpsDown := proc(RR::Matrix, Ju::Vector)::Vector; 
description "Finds the rows of RR where there are downward jumps in multiplicity";
	uses ListTools, LinearAlgebra;
	local aux, bux, vdn, j, ret; 
	aux := [seq(evalb(0 < Ju[j]), j=1..Dimension(Ju))]; 
	bux := [SearchAll(true, aux)]; 
	vdn := nops(bux);
	ret := Vector(vdn); 
	for j to nops(bux) do 
		ret[j] := [RR(bux[j], 1) + 1, Ju[bux[j]]]; 
	end do; 
	return ret; 
end proc; # JumpsDown

JumpsUp := proc(RR::Matrix, Ju::Vector)::Vector; 
description "Finds the rows of RR where there are upward jumps in multiplicity";
	uses ListTools, LinearAlgebra;
	local aux, bux, vdn, j, ret; 
	aux := [seq(evalb(0 < Ju[j]), j=1..Dimension(Ju))]; 
	bux := [SearchAll(true,aux)]; 
	vdn := nops(bux);
	ret := Vector(vdn); 
	for j to nops(bux) do 
		ret[j] := [RR(bux[j], 1), Ju[bux[j]]]; 
	end do; 
	return ret; 
end proc; # JumpsUp

NablEl := proc(L0::set,Hu::set,K::set,X::symbol,n::integer)::list;
description "Inputs: L0 std space, H reg hull (not assumed std), K=K(L0) the diagram of L0, (X,n) geometry; returns [Nabs=Nabla set, Nabl=Nabla list, DenHL=denoms of H restr to L]";
	uses ListTools;
	local stH0, H0, wH, AUX, gH0, i, j, k, gH, RRH, gL0, sub, DenomHR, DenomHRL, Wval, ctsH, Nabl, Nabs, aux, bux;
	if ( evalb(Hu subset {seq(i,i=1..n)}) ) then
		H0 := Hu:
		wH := []:
	else
		stH0 := stdLElemPar(Hu,X,n,K);                                    # W-element sending Hu to a standard H0
		H0   := LWeyl(Hu,stH0,X,n);                                       # compute H0
		wH   := Reverse(stH0);                                            # wH are the W-elements that sends the std hull H0 to H 
	end if; 
	AUX  := stdWDD(H0,X,n);                                           # compute a generic vectors in H0
	gH0  := subs({seq(x[j]=y[j],j=1..n)},parse(convert(AUX,string))); # change variables to allow substitutions afterwards        
	gH   := WDDWeyl(gH0,wH,X,n);                                      # gH generic points in H 
	RRH  := ResRts(gH0,X,n);                                          # RRH is the restr roots in the W-sum for H (via its std form H0)     
	gL0  := stdWDD(L0,X,n);                                           # generic coordinates at L0 centered in the center of L0
	sub  := solve({seq(gH[j]=gL0[j],j=1..n)},{seq(y[j],j=1..n)});     # coordinate transformation for restriction from H to L0 
	DenomHR  := JumpsDown(RRH,JumpsSucc(RRH));                        # computes the denominators of H using the jumps in multiplcity
	DenomHRL := Vector(Dimension(DenomHR)):                           # the next lines restricts the denominators if H to L0
	for k to Dimension(DenomHR) do                                    # 
		Wval := subs(sub, DenomHR[k][1]);                         # 
		if ( type(Wval,numeric) ) then                            #
			if ( evalb(Wval<1) ) then                         # in case a restricted root of H0 becomes constant on L0 
				Wval := 1-Wval;                           # we use the functional equation to put the constantant in the admissible range
			end if;                                           #
		end if;                                                   #
		DenomHRL[k] := Wval;                                      # 
	end do:                                                           #
	aux  := [seq(type(DenomHRL[i],numeric),i=1..Dimension(DenomHRL))]:                                 # find the non-constant gradients
	bux  := [SearchAll(false,aux)]:                                                                    #
	ctsH := [seq(subs({seq(x[j]=0,j=1..n)},parse(convert(DenomHRL[bux[i]],string))) ,i=1..nops(bux))]: # find the constants
	Nabl := [seq(DenomHRL[bux[i]]-ctsH[i],i=1..nops(ctsH))]:                                           # find the list of gradients (denominator minus the constant)
	Nabs := convert(Nabl,set):                                                                         # find the set of gradients 
	return [Nabs,Nabl,ctsH]:
end proc; # NablEl

NablaCs := proc(L0::set,w::list,KL::set,GR::set,J::list,X::symbol,n::integer)::list;
description "Returns [test,Nabla,Hs,Denoms] with Nabla the eligible gradients, Hs a hull for which the grad is admisible, Den the denoms for nabla in the hull and test=true/false for existing adm hull";
	uses ListTools;
	local d, Hall, AUX, GH, H, H1, Nab0, GrTest, Xi, key, Hn, Nn, aux, Rws, Cts, tst, TF, NBs, Hs, Dens, i, j, k, p, q, u;
	# Determination of d-good hulls
	d    := minRcoset(w,X,n,J)[2];                                         # finds d
	Hall := RegHulls(L0,X,n);                                              # inputs all regular hulls of L0
	AUX  := [seq(evalb(LWeyl(Hall[i],d,X,n) subset GR), i=1..nops(Hall))]; # find the d-good hulls
	GH   := [SearchAll(true,AUX)];                                         #   
	H    := [seq(Hall[GH[i]],i=1..nops(GH))];                              # saves the d-good Hulls
	# Computation of eligible gradients, wrt the first good regular hull
	H1   := H[1]:
	Nab0 := NablEl(L0,H1,KL,X,n); # Sorts the eligible gradients by looking at the first good regular hull (more likely to be std)
	# Sweep of the hulls for for admissibility, for each gradient direction
	GrTest := Array(1..nops(Nab0[1]),1..4);								 # Array with the hulls data
	for i from 1 to nops(Nab0[1]) do								 #
		Xi  := Nab0[1][i];									 # Fixes a gradient in Nabla(L,H) for the first good regular hull
		key := 1;                 			  					 # token to end the loop
		k   := 1; 										 #
		while ( evalb(key>0) ) do        							 # loop to search for a good hull for the gradient Xi
			Hn  := H[k];                                                                     # fixes a hull in H
			Nn  := NablEl(L0,H[k],KL,X,n);							 #
			aux := [seq(type(simplify(parse(convert(Nn[2][u],string))/parse(convert(Xi,string))),numeric),u=1..nops(Nn[2]))]; #
			Rws := [SearchAll(true,aux)];							 #
			Cts := Nn[3][Rws];								 #
			tst := [seq(evalb(Cts[u] < 1),u=1..nops(Cts))];					 #
			if ( Search(true,tst)=0 ) then							 # tests if the gradient Xi is admissible for the hull H
				key         := 0;							 #
				GrTest(i,1) := 1;							 #
				GrTest(i,2) := Hn;							 #
				GrTest(i,3) := Nn[2][Rws];						 #
				GrTest(i,4) := Nn[3][Rws];						 #
			end if;										 #
			k := k+1;									 #
			if ( evalb(k > nops(H)) and evalb(key > 0) ) then
				return [false,Nab0[1],0,0];
			end if;
		end do;					 						 #
	end do;												 #
	# Construction of the Output
	TF   := evalb(Search(0,[seq(GrTest(p,1),p=1..RowDimension(GrTest))])=0);					# true/false if all gradients have admissible hull
	NBs  := Nab0[1];												# the set of eligible gradients
	Hs   := [seq(GrTest(p,2),p=1..RowDimension(GrTest))];								# the admissible hulls (ordered wrt NBs)
	Dens := [seq(Vector([seq(GrTest(p,3)[q] + GrTest(p,4)[q],q=1..nops(GrTest(p,3)))]),p=1..RowDimension(GrTest))];	# the denominators in that gradient direction
	return [TF,NBs,Hs,Dens];
end proc; # NablaCs

OrderBound := proc(w::list,Pw::integer)
description "Computes the pole order according to the notes Lemma 13";
# Input the Weyl group element w and Pw, the cardinality of P(w) 
	uses ListTools;
	local R, Rv, gL0, L0, F0, IPs, R4, R5, RefF0, Rmw, Rm4, Rm5, ax4, ax5, Fw, vR, n0, pn4, pn5, dif, Dnw, j;
	## Input the relevant space:
	R     := PoscoRoot(CartMatrix(E,8)):                                                # Positive roots of E8
	Rv    := {seq(j,j=1..120)}:                                                         # Set of all positive roots (as rows of R)
	gL0   := [1,0,0,1,0,0,1,x]:                                                         # Coordinate of the generic vector on L0
	L0    := PoleSet(gL0,R):                                                            # Pole set of L0
	F0    := {2,3,5,6}:                                                                 # Diagram of the fixator
	IPs   := [seq(ListTools:-DotProduct(convert(R[j],list),gL0),j=1..RowDimension(R))]: # Inner-Prods of gL0 with the roots
	R4    := {SearchAll(x+4,IPs)}:                                                      # Set of roots r such that (r,gL0) = x+4
	R5    := {SearchAll(x+5,IPs)}:                                                      # Set of roots r such that (r,gL0) = x+5
	RefF0 := [ [2], [3], [5], [6], [5,6,5] ]:                                           # The 5 reflections of W(F0):
	## Computation of R[x+n](-w) with n=4,5.
	Rmw := {seq(j,j=1..120)} minus Rw(w,E,8): # R(-w)
	Rm4 := Rmw intersect R4;                  # R[x+4](-w)
	Rm5 := Rmw intersect R5;                  # R[x+5](-w)
	## Computation of N(w)
	ax4 := [seq(evalb(LWeyl(Rm4,RefF0[j],E,8)=Rm4),j=1..nops(RefF0))]:         # Test which reflections of W(F0) stabilizes R[x+4](-w)
	ax5 := [seq(evalb(LWeyl(Rm5,RefF0[j],E,8)=Rm5),j=1..nops(RefF0))]:         # Test which reflections of W(F0) stabilizes R[x+5](-w)
	Fw  := [SearchAll(true,[seq(evalb(ax4[j] and ax5[j]),j=1..nops(RefF0))])]; # Fw is the the set of all reflections of F0 that stabilizes both sets
	## Computation of Delta[n0](w)
	vR  := R.SimpcoRoot(E,8):                                                            # input the roots as vectors
	n0  := Coord2WDD(vR[120]-vR[7]-vR[8],E,8):                                           # express the normal direction as a WDD
	pn4 := `add`(seq(ListTools:-DotProduct(n0,convert(R[Rm4[j]],list)),j=1..nops(Rm4))); # computes (n0,r) with r in R[x+4](-w)
	pn5 := `add`(seq(ListTools:-DotProduct(n0,convert(R[Rm5[j]],list)),j=1..nops(Rm5))); # computes (n0,r) with r in R[x+5](-w)
	dif := pn5 - pn4;                                                                    # compute Delta[n0](w)
	if evalb(dif=0) then
        	Dnw := 0:
	else
	        Dnw := 1:
	end if;
	## The equation is RHS = |R[x+5](-w)| - |R[x+4](-w)| + min(0, max(N(w),P(w)) - 5 - Dn(w))
	return nops(Rm5) - nops(Rm4) + min( 0, max(Pw,nops(Fw)) - 5 - Dnw);
end proc; # OrderBound

Perp2pRts := proc(L::set,p::list,Y::symbol,m::integer,K::list,X::symbol,n::integer) 
description "returns the set of roots (reflections) orthogonal to both L and p";
	uses ListTools;
	local S, R, aux, j, Rp, Sp, zer;
	S   := CstAndPerp(L,X,n)[2];
	R   := PoscoRoot(CartMatrix(X,n));
	Rp  := convert(YminXn(Y,m,K,X,n),set);
	Sp  := S intersect Rp;
	aux := [seq(DotProduct(p,convert(R[Sp[j]],list)),j=1..nops(Sp))];
	zer := [SearchAll(0,aux)];
	return {seq(Sp[zer[j]],j=1..nops(zer))}; 
end proc; # Perp2pRts

PolesCrossed := proc(L::set,pini::list,pfin::list,Num::list,Den::list,X::symbol,n::integer)::Array; 
description "returns an array with 7 columns: #1 a pole M spawned, #2. pt of crossing, #3. the root crossed to form M, #4. the order of the crossing, #5.The 3-list NUM at the crossing, #6. The 3-List DEN at the crossing, #7 a tag true/false indicating if the movement is parallel to the crossing.";
# The input is:
# L: Pole set, pini: initial point, pfin: final point, Num: a 3-list with numerators on L, Den: a 3-list with denominators on L, (X,n): geometry
# IMPORTANT: Num and Den already cancelled the common factors and they consist of roots, NOT of the linear factors at a generic point of L
# The input for Den and Num *MUST NOT* contain constant factors 
# The last column PAR will not be transferred to Gen. Rather, it will be the PAR column of Std
	uses ListTools;
	local R, gL, aux, nc, i, j, k, DGp, DGm, DFm, Rcr, Ms, Pts, FGN, FGD, M, pM, gM, zer, pol, numM, denM, canc, posN, posD, NumM, DenM, oMs, ord, ret, prd, PAR;
	R := PoscoRoot(CartMatrix(X,n));
	# The next lines search for the denominators that produce crossings; a value <= 0 indicates a crossing
	DGp := [seq( (DotProduct(pini,convert(R[Den[1][i]],list))+1)*(DotProduct(pfin,convert(R[Den[1][i]],list))+1) ,i=1..nops(Den[1]))]; # Den[1]
	DGm := [seq( (DotProduct(pini,convert(R[Den[2][i]],list))-1)*(DotProduct(pfin,convert(R[Den[2][i]],list))-1) ,i=1..nops(Den[2]))]; # Den[2]
	DFm := [seq( (DotProduct(pini,convert(R[Den[3][i]],list))-1)*(DotProduct(pfin,convert(R[Den[3][i]],list))-1) ,i=1..nops(Den[3]))]; # Den[3]
	Rcr := []; # stores the affine root hyperplane crossed
	Ms  := []; # stores the space produced in the crossing
	Pts := []; # stores the initial point of the crossing
	FGN := []; # stores the numerator of the function FG on the new space crossed (after cancellations)
	FGD := []; # stores the denominator of the function FG on the new space crossed (after cancellations)
	oMs := []; # stores the pole-order of the new space crossed
	PAR := []; # stores a tag indicating if the segment of movement is parallel to the crossing
	for k from 1 to nops(Den[1]) do
		if ( DGp[k]<=0 ) then
			M    := PoleSet(Coord2WDD(GenPt(L union {-Den[1][k]},X,n),X,n),R);                        # computes M, the pole roots of the spawned space 
			gM   := Coord2WDD(GenPt(M,X,n),X,n);                                                      # computes generic point in M
			numM := [seq([seq(DotProduct(gM,convert(R[Num[j][i]],list)),i=1..nops(Num[j]))],j=1..3)]; # computes the numerator of F.G|M
                        denM := [[seq(DotProduct(gM,convert(R[Den[1][i]],list))+1,i=1..nops(Den[1]))],            # computes the denominator of F.G|M
                                 [seq(DotProduct(gM,convert(R[Den[2][i]],list))-1,i=1..nops(Den[2]))],            #
                                 [seq(DotProduct(gM,convert(R[Den[3][i]],list))-1,i=1..nops(Den[3]))]];           #
			zer  := nops([SearchAll(0,[op(numM[1]),op(numM[2]),op(numM[3])])]);			  # counts the number of zeroes in the numerators
			pol  := nops([SearchAll(0,[op(denM[1]),op(denM[2]),op(denM[3])])]);			  # counts the number of poles in the numerators
			ord  := pol - zer - 1; 								          # computes the pole order
			if ( evalb(ord>=0) ) then								  # checks if M is indeed a pole space
				Rcr  := [op(Rcr),-Den[1][k]];                                                     # stores the crossing pole root hyperplane 
				Ms   := [op(Ms),M];                                                               # stores the spawned space M
				oMs  := [op(oMs),ord];								  # stores the pole order M
				pM   := PtInter("neg",pini,pfin,Den[1][k],X,n);                                   # computes the point of intersection (according to sign) in [pini,pfin]
				Pts  := [op(Pts),pM];                                                             # stores the point of crossing pM
				canc := CancThreeL(numM,denM);                                                    # cancels the common factors of F.G|M and remove constant factors
				posN := canc[2][1];                                                               # 
				posD := canc[2][2];                                                               #
				NumM := [seq([seq(Num[j][posN[j][i]],i=1..nops(posN[j]))],j=1..3)];               # computes numerator of F.G|M
                        	FGN  := [op(FGN),NumM];                                                           # stores the numerator
                        	DenM := [seq([seq(Den[j][posD[j][i]],i=1..nops(posD[j]))],j=1..3)];               # computes denominator of F.G|M
				FGD  := [op(FGD),DenM];                                                           # stores the denominator
				if ( evalb(DotProduct(pini,convert(R[Den[1][k]],list))+1=DotProduct(pfin,convert(R[Den[1][k]],list))+1) ) then
					PAR := [op(PAR),true];  # if the crossed root is zero both in the initial and end point PAR = 'true' 
				else
					PAR := [op(PAR),false]; # if not, PAR = 'false'
				end if;
			end if;
		end if;
	end do;	
	for k from 1 to nops(Den[2]) do
		if ( DGm[k]<=0 ) then
			M    := PoleSet(Coord2WDD(GenPt(L union {Den[2][k]},X,n),X,n),R);                         # computes M, the pole roots of the spawned space 
			gM   := Coord2WDD(GenPt(M,X,n),X,n);                                                      # computes generic point in M
			numM := [seq([seq(DotProduct(gM,convert(R[Num[j][i]],list)),i=1..nops(Num[j]))],j=1..3)]; # computes the numerator of F.G|M
                        denM := [[seq(DotProduct(gM,convert(R[Den[1][i]],list))+1,i=1..nops(Den[1]))],            # computes the denominator of F.G|M
                                 [seq(DotProduct(gM,convert(R[Den[2][i]],list))-1,i=1..nops(Den[2]))],            #
                                 [seq(DotProduct(gM,convert(R[Den[3][i]],list))-1,i=1..nops(Den[3]))]];           #
			zer  := nops([SearchAll(0,[op(numM[1]),op(numM[2]),op(numM[3])])]);			  # counts the number of zeroes in the numerators
			pol  := nops([SearchAll(0,[op(denM[1]),op(denM[2]),op(denM[3])])]);			  # counts the number of poles in the numerators
			ord  := pol - zer - 1; 								          # computes the pole order
			if ( evalb(ord>=0) ) then								  # checks if M is indeed a pole space
				Rcr  := [op(Rcr),Den[2][k]];                                                      # stores the crossing pole root hyperplane 
				Ms   := [op(Ms),M];                                                               # stores the spawned space M
				oMs  := [op(oMs),ord];								  # stores the pole order M
				pM   := PtInter("pos",pini,pfin,Den[2][k],X,n);                                   # computes the point of intersection (according to sign) in [pini,pfin] 
				Pts  := [op(Pts),pM];                                                             # stores the point of crossing pM
				canc := CancThreeL(numM,denM);                                                    # cancels the common factors of F.G|M and remove constant factors
				posN := canc[2][1];                                                               # 
				posD := canc[2][2];                                                               #
				NumM := [seq([seq(Num[j][posN[j][i]],i=1..nops(posN[j]))],j=1..3)];               # computes numerator of F.G|M
				FGN  := [op(FGN),NumM];                                                           # stores the numerator
				DenM := [seq([seq(Den[j][posD[j][i]],i=1..nops(posD[j]))],j=1..3)];               # computes denominator of F.G|M
				FGD  := [op(FGD),DenM];                                                           # stores the denominator
				if ( evalb(DotProduct(pini,convert(R[Den[2][k]],list))-1=DotProduct(pfin,convert(R[Den[2][k]],list))-1) ) then
					PAR := [op(PAR),true];  # if the crossed root is zero both in the initial and end point PAR = 'true' 
				else
					PAR := [op(PAR),false]; # if not, PAR = 'false'
				end if;

			end if;
		end if;
	end do;
	for k from 1 to nops(Den[3]) do
		if ( DFm[k]<=0 ) then
			M    := PoleSet(Coord2WDD(GenPt(L union {Den[3][k]},X,n),X,n),R);                         # computes M, the pole roots of the spawned space 
			gM   := Coord2WDD(GenPt(M,X,n),X,n);                                                      # computes generic point in M
			numM := [seq([seq(DotProduct(gM,convert(R[Num[j][i]],list)),i=1..nops(Num[j]))],j=1..3)]; # computes the numerator of F.G|M
                        denM := [[seq(DotProduct(gM,convert(R[Den[1][i]],list))+1,i=1..nops(Den[1]))],            # computes the denominator of F.G|M
                                 [seq(DotProduct(gM,convert(R[Den[2][i]],list))-1,i=1..nops(Den[2]))],            #
                                 [seq(DotProduct(gM,convert(R[Den[3][i]],list))-1,i=1..nops(Den[3]))]];           #
			zer  := nops([SearchAll(0,[op(numM[1]),op(numM[2]),op(numM[3])])]);			  # counts the number of zeroes in the numerators
			pol  := nops([SearchAll(0,[op(denM[1]),op(denM[2]),op(denM[3])])]);			  # counts the number of poles in the numerators
			ord  := pol - zer - 1; 								          # computes the pole order
			if ( evalb(ord>=0) ) then								  # checks if M is indeed a pole space
				Rcr  := [op(Rcr),Den[3][k]];                                                      # stores the crossing pole root hyperplane 
				Ms   := [op(Ms),M];                                                               # stores the spawned space M
				oMs  := [op(oMs),ord];								  # stores the pole order M
				pM   := PtInter("pos",pini,pfin,Den[3][k],X,n);                                   # computes the point of intersection (according to sign) in [pini,pfin] 
				Pts  := [op(Pts),pM];                                                             # stores the point of crossing pM
				canc := CancThreeL(numM,denM);                                                    # cancels the common factors of F.G|M and remove constant factors
				posN := canc[2][1];                                                               # 
				posD := canc[2][2];                                                               #
				NumM := [seq([seq(Num[j][posN[j][i]],i=1..nops(posN[j]))],j=1..3)];               # computes numerator of F.G|M
				FGN  := [op(FGN),NumM];                                                           # stores the numerator
				DenM := [seq([seq(Den[j][posD[j][i]],i=1..nops(posD[j]))],j=1..3)];               # computes denominator of F.G|M
				FGD  := [op(FGD),DenM];                                                           # stores the denominator
				if ( evalb(DotProduct(pini,convert(R[Den[3][k]],list))-1=DotProduct(pfin,convert(R[Den[3][k]],list))-1) ) then
					PAR := [op(PAR),true];  # if the crossed root is zero both in the initial and end point PAR = 'true' 
				else
					PAR := [op(PAR),false]; # if not, PAR = 'false'
				end if;
			end if;
		end if;
	end do;
	if ( evalb(nops(Ms)=0) ) then 
		return Array();
	end if;
	ret := Array(1..nops(Ms),1..7);
	for i from 1 to nops(Ms) do
		ret(i,1) := Ms[i];
		ret(i,2) := Pts[i]; 
		ret(i,3) := Rcr[i];
		ret(i,4) := oMs[i];
		ret(i,5) := FGN[i];
		ret(i,6) := FGD[i];
		ret(i,7) := PAR[i];
	end do;
	return ret;
end proc; # PolesCrossed

PtInter := proc(opt::string,p::list,q::list,r::integer,X::symbol,n::integer)
description "returns the point of intersection between [p,q] and {r=1}; assumes r is s.t. this intersection is non-empty";
	uses LinearAlgebra;
	local sinal, R, v, s, k, T, Pt, ret;
	if ( evalb(opt="pos") ) then
		sinal := 1;
	elif ( evalb(opt="neg") ) then 
		sinal := -1;
	else
		return ERROR("The first entry 'option' should be either p (plus) or m (minus)");
	end if;
	R  := PoscoRoot(CartMatrix(X,n));
	v  := [seq((1-s)*p[k]+s*q[k],k=1..n)];
	T  := solve(ListTools:-DotProduct(convert(Row(R,r),list),v)=sinal,s);
	Pt := subs(s=T,[seq(v[k],k=1..n)]);
	return Pt;	
end proc; # PtInter

RelevExcN := proc(L::list,orb::list)::list;
description "Given a list with Weyl group elements of W(E6)^{F0} (transversal to F0) of length <= n construct a list with length <= n+1 in which all elements satisfy |P(w)| <= 3";
# This procedure is for the exceptional space N = [1,0,0,1,0,1,x,y] with stabilizer generated by F0 = {2,3,5}
# Here, L = [ [L[1], L[2], L[3], L[4], L[5]] ] is a list of quintuples with 
# L[1] := w a Weyl group element (described as a word)
# L[2] := length of w
# L[3] := |P(w)|
# L[4] := w(g), with g = [1,1,1,1,1,1,1,1] being the Weyl vector
# L[5] := w(F0)
	uses ListTools, LinearAlgebra;
	local N, F0, j, ToDo, nOrb, newL, i, g, w, p, F, l;
	N    := {1, 4, 6, 9, 10, 11, 12, 13, 17, 18, 19, 25};                              # Pole set of N
	F0   := {2, 3, 5};                                                                 # Diagram of the fixator
	ToDo := L;                                                                         # Input elements of length n
	nOrb := orb;                                                                       # Lists the chamber corresponding to w (to give uniqueness of the each word [w])
	newL := []:
	j    := 1:
	while ( evalb(j<=nops(ToDo)) ) do
		#0. Attempt to enlarge list by simple reflections in W(E6)
		for i from 1 to 6 do
			#1. Check first if [i,w] produces an element in W(E6)/F0
			if ( not evalb(i in ToDo[j][5]) ) then
				g := WDDWeyl(ToDo[j][4],[i],E,8);
				#2. Check if [w']=[i,w] produces a new element
				if ( not member(g,nOrb) ) then
					#3. Check if [w'] = [i,w] sends a root of P(N) to negative, to compute p = |P(w)|
					if ( evalb(op(LWeyl({i},Reverse(ToDo[j][1]),E,8)) in N) ) then
						p := ToDo[j][3] + 1;
					else
						p := ToDo[j][3];
					end if;
					#4. Decide whether or not to add [w] to list, depending on p <= 3 criterion
					if ( evalb(p<=3) )then
						w    := [i,op(ToDo[j][1])]; 
						F    := LWeyl(ToDo[j][5],[i],E,8);
						l    := [ w,nops(w),p,g,F ];
						newL := [op(newL),l];            # included a new element to L
						nOrb := [op(nOrb),g];            # included a new element in the orbit
					end if;
				end if;
			end if; 
		end do;
		j := j+1;
	end do;
	return [newL,nOrb];
end proc; # RelevExcN

RelevExc := proc(L::list,orb::list)::list;
description "Given a list with Weyl group elements of W(E7)^{F0} (transversal to F0) of length <= n construct a list with length <= n+1 in which all elements satisfy |P(w)| <= 6";
# This procedure is for the exceptional space L0 = [1,0,0,1,0,0,1,x] with stabilizer generated by F0 = {2,3,5,6}
# Here, L = [ [L[1], L[2], L[3], L[4], L[5]] ] is a list of quintuples with 
# L[1] := w a Weyl group element (described as a word)
# L[2] := length of w
# L[3] := |P(w)|
# L[4] := w(g), with g = [1,1,1,1,1,1,1,1] being the Weyl vector
# L[5] := w(F)0
	uses ListTools, LinearAlgebra;
	local L0, F0, j, ToDo, nOrb, newL, i, g, w, p, F, l;
	L0   := {1, 4, 7, 9, 10, 11, 12, 14, 17, 18, 19, 20, 21, 25, 26, 27, 33};          # Pole set of L0
	F0   := {2,3,5,6};                                                                 # Diagram of the fixator
	ToDo := L;                                                                         # Input elements of length n
	nOrb := orb;                                                                       # Lists the chamber corresponding to w (to give uniqueness of the each word [w])
	newL := []:
	j    := 1:
	while ( evalb(j<=nops(ToDo)) ) do
		#0. Attempt to enlarge list by simple reflections in W(E7)
		for i from 1 to 7 do
			#1. Check first if [i,w] produces an element in W(E7)/F0
			if ( not evalb(i in ToDo[j][5]) ) then
				g := WDDWeyl(ToDo[j][4],[i],E,8);
				#2. Check if [w']=[i,w] produces a new element				
				if ( not member(g,nOrb) ) then
					#3. Check if [w'] = [i,w] sends a root of P(L0) to negative, to compute p = |P(w)|
					if ( evalb(op(LWeyl({i},Reverse(ToDo[j][1]),E,8)) in L0) ) then
						p := ToDo[j][3] + 1;
					else
						p := ToDo[j][3];
					end if;
					#4. Decide whether or not to add [w] to list, depending on p <= 6 criterion
					if ( evalb(p<=6) )then
						w    := [i,op(ToDo[j][1])]; 
						F    := LWeyl(ToDo[j][5],[i],E,8);
						l    := [ w,nops(w),p,g,F ];
						newL := [op(newL),l];            # included a new element to L
						nOrb := [op(nOrb),g];            # included a new element in the orbit
					end if;				end if;
			end if; 
		end do;
		j := j+1;
	end do;
	return [newL,nOrb];
end proc; # RelevExc

RtRefl := proc(p::Vector,r::integer,X::symbol,n::integer)
description "returns the reflection on the root r";
	uses LinearAlgebra;
	local R, ret;
	R   := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
	ret := p - 2*DotProduct(R[r],p)/DotProduct(R[r],R[r])*R[r]; 
	return ret;
end proc; # RtRefl

RtReflL := proc(L::set,r::integer,X::symbol,n::integer)
description "Computes the action of the reflection of the root r on the set of roots L";
	local j;
	return {seq(RtReflPerm(L[j],r,X,n),j=1..nops(L))};
end proc; # RtReflL

#RtReflL := proc(L::set,r::integer,X::symbol,n::integer)
#description "Computes the action of the reflection of the root r on the set of roots L";
#	uses ListTools, LinearAlgebra;
#	local Rp, N, Rm, R, rL, v, i, aux;
#	Rp := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
#	N  := RowDimension(Rp);
#	Rm := <seq((-1)*Rp[N-i+1],i=1..N)>; # we order the negative roots so that -1 is the last row and -N is the first row
#	R  := <Rp,Rm>;                     # the ordering of the rows is 1, 2, ... , N-1, N | -N, -N+1, ... -2, -1
#	rL := Vector(nops(L));
#	for i from 1 to nops(L) do
#		v   := R[L[i]];	
#		aux := Search(parse(convert(RtRefl(v,r,X,n),string)),[seq(parse(convert(R[j],string)),j=1..RowDimension(R))]);
#		if evalb(aux>N) then
#			rL[i] := (-1)*(2*N-aux+1);	
#		else
#			rL[i] := aux;	
#		end if;
#	end do; 
#	return {seq(rL[i],i=1..Dimension(rL))};
#end proc; # RtReflL

RtReflPerm := proc(k::integer,r::integer,X::symbol,n::integer)
description "Computes the action of the root r in the root labeled by k in {-N,...,-1,1,..,N} with N = |R+|";
	# If a matrix of permutation of roots exist, then use it. Otherwise, construct it the first time used and store.
	uses ListTools, LinearAlgebra, FileTools;
	local s, Shf, N, Rp, Rm, R, rL, v, i, j, aux;
	s   := cat("CascData/",X,n,"/RtRefl",r,".mpl");
	# (08.05.25) Here we made the ramification to construct if does not exist or read if exists.
	if not Exists(s) then
		Rp  := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
		N   := RowDimension(Rp);
		Rm  := <seq((-1)*Rp[N-i+1],i=1..N)>; # we order the negative roots so that -1 is the last row and -N is the first row
		R   := <Rp,Rm>;                      # the ordering of the rows is 1, 2, ... , N-1, N | -N, -N+1, ... -2, -1
		Shf := [seq(Search(convert( RtRefl(R[i],r,X,n), list) , [seq( convert( R[j] , list) , j=1..RowDimension(R) )]) , i = 1..RowDimension(R))];	
		Export(s,Shf):
	else
		Shf := Read(s);
	end if;
	N   := nops(Shf)/2;
	if ( evalb(Shf[k]>N) ) then
		return (-1)*(2*N - Shf[k] +1);
	else
		return Shf[k];
	end if;
end proc; # RtReflPerm

RwSpeed := proc(w::list,X::symbol,n::integer)::set;
description "given a Weyl group element w, returns the set of positive roots sent to negative by w";
	local aux, N, Rts, r;
	uses ListTools, LinearAlgebra;
	N   := RowDimension(PoscoRoot(CartMatrix(X,n))):
	aux := [seq(op(LWeylSpeed({r},w,X,n)),r=1..N)]:
	Rts := {seq(r,r=1..N)}:
	return {SearchAll(false,[seq(evalb(aux[r] in Rts) ,r=1..N)])};
end proc; # RwSpeed

SortDenVec := proc(Den::Vector,n::integer)
	uses ListTools;
	local d, i, j, csts, aux, bux, srtd, grds, mult, ret;
	d    := Dimension(Den);
	csts := [seq(subs({seq(x[j]=0,j=1..n)},parse(convert(Den[i],string))),i=1..d)];
	aux  := convert(csts,set);
	bux  := [seq(SearchAll(aux[i],csts),i=1..nops(aux))];
	srtd := [seq(Den[bux[i]],i=1..d)];
	csts := [seq(subs({seq(x[j]=0,j=1..n)},parse(convert(srtd[i],string))),i=1..d)];
	grds := [seq(srtd[i]-csts[i],i=1..d)];
	mult := [seq(subs({seq(x[j]=1,j=1..n)},parse(convert(grds[i],string))),i=1..d)];
	aux  := convert(mult,set);
	srtd := [seq(SearchAll(aux[i],mult),i=1..nops(aux))];
	ret  := Vector(d);
	for i from 1 to d do
		ret[i] := grds[srtd[i]] + csts[srtd[i]];
	end do;
	return ret;
end proc; # SortDenVec

WeylRt := proc(r::integer,w::list,X::symbol,n::integer)::integer;
description "returns the action of the Weyl group element w on the root r";
	local s, j;
	s := proc(r,i::integer)::Vector;
		RtReflPerm(r,i,X,n);
	end proc;
	foldl(s,r,seq(w[-j],j=1..nops(w)));
end proc; # WeylRt

LWeylSpeed := proc(L::set,w::list,X::symbol,n::integer)::set;
description "conjugates the residual space L = {PoleSet(L)} by w";
	local j;
	return {seq( sign(L[j])*WeylRt(abs(L[j]),w,X,n) ,j=1..nops(L))};
end proc; # LWeylSpeed

SUBTag := proc(L::set,S::Array,Y::symbol,m::integer,K::list,X::symbol,n::integer) 
description "adds a tag 'true' or 'false' to the space L according to the Std Array at the moment when L is analysed";
# 'true' if L is residual or a subspace of a W' conjugate of a residual space in Std with same center  and 'false' otherwise
	uses ArrayTools, ListTools;
	local dcL, ds, i, r, aux, res, dcM, crit, dist, test, Wp;
	if ( IsRes(L,X,n) ) then
		return true;
	else 
		if ( evalb(nops(Dimensions(S))=0) ) then
			return false;
		end if;
		dcL := WDDDom(Coord2WDD(CentL(L,X,n),X,n),X,n);       				 # computes dominant center of L
		ds  := [seq(DimL(S(i,1),X,n),i=1..RowDimension(S))]; 				 # computes the dimensions of the spaces in S=Std	
		r   := Search(DimL(L,X,n),ds);                  				 # finds the first entry with same dimension as L                 
		if ( evalb(r=0) ) then                           				 #
			r := RowDimension(S)+1;                                                  # 
		end if;                                         				 #
		aux  := [seq(IsRes(S(i,1),X,n),i=1..r-1)];                                       # compute if the spaces of dim>dim(L) are residual or not
		res  := [SearchAll(true,aux)];                                                   # res[i],i=1..nops(res) are the residuals with dim > dim(L)
		dcM  := [seq(WDDDom(Coord2WDD(CentL(S(res[i],1),X,n),X,n),X,n),i=1..nops(res))]; # computes the dominant center of the residuals
		aux  := [seq(evalb(dcL=dcM[i]),i=1..nops(dcM))];				 # checks if dcM = dcL
		crit := [SearchAll(true,aux)]; 							 # res[crit[i]],i=1..nops(crit) are residuals with same dominant center as L
		if ( evalb(nops(crit)=0) ) then
			return false;
		else
			Wp   := convert(YminXn(Y,m,K,X,n),set);
			dist := [seq(DistWSL(L,S(res[crit[i]],1),Y,m,K,X,n,Wp)[2],i=1..nops(crit))];               # compute the W' from L and the critical Ms
			test := [seq(evalb(LWeyl(S(res[crit[i]],1),dist[i],X,n) subset L),i=1..nops(dist))]; # checks if L is in the W' orbit of a critical MM
			r    := Search(true,test);
			if ( evalb(r=0) ) then
				return false;
			else
				return true;
			end if;
		end if;
	end if;
end proc; # SUBTag

tDenoms := proc(L0::set,w::list,GR::set,K::set,Y::symbol,m::integer,Ky::list,X::symbol,n::integer)
description "Compute the 'tilde' denominators for the W-sum (tDen) and for the W'-sum (tDenp) on L0";
# Here (L0,w) is a standard pair (s.t. L=wL0 is a space in Casc) and the variables x[1],... are such that sending them to zero we reach centre of L0
# Also, the set of good roots GR is an input to avoid needing to compute all the time. As well as K = K(L0) the parabolic subdiagram defined by L0.
# We compute:
# a. The d of minimal length in W'w
# b. The set H of all good regular hulls of L0
# c. The data (H0, dH) of std representation of good regular hulls and their respective d's
# d. Generic vectors of each good regular hull
# e. The restricted roots for the W-sum for each standard good regular hull
# f. The restricted roots for the W'-sum for each standard good regular hull
# g. The set tDen given as the intersection of Den over all standard good regular hulls H0
# h. The set tDenp given as the intersection of Den over all standard good regular hulls H0
	uses LinearAlgebra, ListTools;
	local J, d, Hall, AUX, GH, H, stdH, H0, wH, dH, RdH, gH0, gH, RRH, RRdH, gL0, sub, Wval, Wpval, DenomHR, DenomHRL,DenomHRd, DenomHRdL, tDen, tDenp, i, j, k;
	if ( n=6 ) then
		J := [2,3,4,5,6];
	else
		J := [seq(j,j=1..n-1)];
	end if;
	d    := minRcosetSpeed(w,X,n,J)[2];                                                                    # a.
	Hall := RegHulls(L0,X,n);                                                                              # b1. construct first all regular hulls of L0
	AUX  := [seq(evalb(LWeyl(Hall[i],d,X,n) subset GR), i=1..nops(Hall))];                                 # b2.
	GH   := [SearchAll(true,AUX)];                                                                         # b3. select the ones contained in the good roots  
	H    := [seq(Hall[GH[i]],i=1..nops(GH))];                                                              # b4. H stores the good regular hulls
	stdH := [seq(stdLElemPar(H[i],X,n,K),i=1..nops(H))];                                                   # c1. compute the element in W(K(L0)) that puts each hull in std position
	H0   := [seq(LWeyl(H[i],stdH[i],X,n),i=1..nops(H))];                                                   # c2. H0 is the standard representative for each good regular hull
	wH   := [seq(Reverse(stdH[i]), i = 1 .. nops(H))];                                                     # c3. wH are the W-elements that sends the std hull H0 to H; wH[i](H0[i])=H[i]  
	dH   := [seq(minRcoset([op(d),op(wH[i])],X,n,J)[2],i=1..nops(H))];                                     # c4. dH is the min rep in W'(dwH); up to W' conjugation, dwH(H0) contains a space in Casc 
	RdH  := [seq(Rw(dH[i],X,n) union LWeyl(convert(YminXn(Y,m,Ky,X,n),set),Reverse(dH[i]),X,n),i =1..nops(H))]; # c5. construct Rd for each H; these are the roots relevant to the W'-sum
	AUX  := [seq(stdWDD(H0[i],X,n),i=1..nops(H))];                                                         # d1. compute generic vectors in each hull
	gH0  := [seq(subs({seq(x[j]=y[j],j=1..n)},parse(convert(AUX[k],string))),k=1..nops(AUX))];             # d2. change variables to allow substitutions afterwards
	gH   := [seq(WDDWeyl(gH0[i],wH[i],X,n),i=1..nops(H))];                                                 # d3. gH generic points in each good regular hull 
	RRH  := [seq(ResRts(gH0[i],X,n),i=1..nops(H))];                                                        # e.  RRH is the restr rts in the W-sum for each H
	RRdH := [seq(Matrix(RowDimension(RRH[i]),2),i=1..nops(H))];                                            # f.  RRdH stores the restr rts in the W'-sum (uses the 'd'); constructed in the loop 
	for i to nops(H) do
		for k to RowDimension(RRH[i]) do 
			RRdH[i](k,1) := RRH[i](k,1); 
			RRdH[i](k,2) := RRH[i](k,2) intersect RdH[i]; 
		end do;
	end do;
	gL0      := stdWDD(L0,X,n);                                                              # generic coordinates at L0 centered in the center of L0
	sub      := [seq(solve({seq(gH[i][j]=gL0[j],j=1..n)},{seq(y[j],j=1..n)}),i=1..nops(H))]; # coordinate substitution to restrict the denominators from each H to L0
	DenomHR  := [seq(JumpsDown(RRH[i],JumpsSucc(RRH[i])),i=1..nops(H))];                     # g1. computes the denominators of W-sum of each good regular hull using the jumps in multiplcity
	DenomHRL := [seq(Vector(Dimension(DenomHR[i])),i=1..nops(H))];                           # g2. restrict to L each expression (done inside the loop)
	for i to nops(H) do                                                                      #
		for k to Dimension(DenomHR[i]) do                                                # 
			Wval := subs(sub[i], DenomHR[i][k][1]);                                  # 
			if ( type(Wval,numeric) ) then                                           #
				if ( evalb(Wval<1) ) then                                        # in case a restricted root of H0 becomes constant on L0 
					Wval := 1-Wval;                                          # we use the functional equation to put the constantant in the admissible range
				end if;                                                          #
			end if;                                                                  #
			DenomHRL[i][k] := [Wval, DenomHR[i][k][2]];                              #
		end do;                                                                          #
	end do;                                                                                  #
	tDen      := HullInter(HullCollapse(DenomHRL));                                          # g3. intersect the denominators of W-sum in each hull
	DenomHRd  := [seq(JumpsUp(RRdH[i],JumpsPred(RRdH[i])),i=1..nops(H))];                    # h1. computes the denominators of W-sum of each good regular hull using the jumps in multiplcity
	DenomHRdL := [seq(Vector(Dimension(DenomHRd[i])),i=1..nops(H))];                         # h2. restrict to L each expression (done inside the loop)
	for i to nops(H) do                                                                      #
		for k to Dimension(DenomHRd[i]) do                                               #
			Wpval := subs(sub[i], DenomHRd[i][k][1]);                                #
			if ( type(Wpval,numeric) ) then                                          #
				if ( evalb(Wpval>0) ) then                                       # in case a restricted root of H0 becomes constant on L0 
					Wpval := 1-Wpval;                                        # we use the functional equation to put the constantant in the admissible range
				end if;                                                          #
			end if;                                                                  #
			DenomHRdL[i][k] := [Wpval, DenomHRd[i][k][2]];                           #
		end do;                                                                          #
	end do;                                                                                  #
	tDenp := HullInter(HullCollapse(DenomHRdL));                                             # h3. intersect the denominators of W'-sum in each hull
	return [tDen,tDenp];
end proc; # tDenoms

WE8dec := proc(v::list)
description "given any element w in WE8 decompose as Eta.Tau.u with Eta in W8/7 minimal, Tau in W7/6 and u in E6";
# Here r0 = {120} (highest root), r8 = {8}, rh6 = {1,2,3,4,5,6,64,108} is the Weyl vector of E6
	uses ListTools;
	local W87, PHI, W76, PSI, W6, GAM, R, r0, r8, rh6, Eta, Tau, u;
	W87 := Read("MCR/E8/lMCRE8.mpl"):
	PHI := Read("MCR/E8/W87orb.mpl"):
	W76 := Read("MCR/E7/lMCRE7.mpl"):
	PSI := Read("MCR/E8/W76orb.mpl"):
	W6  := Read("WeylGroups/WE6.mpl"):
	GAM := Read("MCR/E8/rho6orb.mpl"):
	R   := PoscoRoot(CartMatrix(E,8)):	
	r0  := {120}:
	r8  := {8}:
	rh6 := {1, 2, 3, 4, 5, 6, 64, 108}:
	Eta := W87[Search(op(LWeylSpeed(r0,v,E,8)),PHI)]:
	Tau := W76[Search(op(LWeylSpeed(r8,[op(Reverse(Eta)),op(v)],E,8)),PSI)]:
	u   := W6[Search(LWeylSpeed(rh6,[op(Reverse(Tau)),op(Reverse(Eta)),op(v)],E,8),GAM)]:
	return [Eta,Tau,u];
end proc; # WE8dec

WpConjug := proc(L::set,M::set,Y::symbol,m::integer,K::list,X::symbol,n::integer)
description "Given two spaces L and M returns [TEST,w] where TEST = true/false for being in the same W'-orbit and w in Wp is an element realizing L in W'M, ie, L = wM";
	uses ListTools;
	local dist, ret;
	ret := Vector(2);
	if ( WtEq(L,M,X,n) ) then
		dist :=	DistWSL(L,M,Y,m,K,X,n,convert(YminXn(Y,m,K,X,n),set));
		if ( dist[1] ) then
			return dist;
		else
			ret[1] := dist[1];
			ret[2] := [];
			return ret;
		end if;
	else
		ret[1] := false; ret[2] := [];
		return ret;
	end if;
end proc; # WpConjug

WtEq := proc(L::set,M::set,X::symbol,n::integer)
description "given two spaces L, M returns if L and M has the same inner products with the fundamental weight that characterizes R'";
        uses LinearAlgebra, ListTools;
        local R, p, SL, SM, IPL, IPM, sIPL, sIPM, j, ret, s;
        R := PoscoRoot(CartMatrix(X,n));
        if ( n=6 ) then
                p := convert(IdentityMatrix(n)[1],list);
        else
                p := convert(IdentityMatrix(n)[n],list);
        end if;
        SL := nops(L);
        SM := nops(M);
        if ( SL=SM ) then
                s    := SL;
                IPL  := [seq(sign(L[j])*DotProduct(convert(R[abs(L[j])],list),p),j=1..s)];
                sIPL := sort(IPL);
                IPM  := [seq(sign(M[j])*DotProduct(convert(R[abs(M[j])],list),p),j=1..s)];
                sIPM := sort(IPM);
                if (evalb(sIPL=sIPM) ) then
                        ret := true;
                else
                        ret := false;
                end if;
        else
                ret := false;
        end if;
        return ret;
end proc; # WtEq

# The code below works exactly as v6, but with the sanitation of the code (it had redundant lines for the residual and sub=true cases
#CascPhase := proc(k::integer,Y::symbol,m::integer,K::list,X::symbol,n::integer)
#description "Reads the information stored in Genk.mpl and constructs Std(k).mpl and Gen(k+1).mpl. Here k runs from 0 to n-1";
## added to v4: when deciding if a new entry on Std is to be made, make sure that there is not a previous entry which is W'-conjugate to it 
#	uses LinearAlgebra, ListTools;
#	local i, j, R, Rv, wt, s, Std, Gen, NO, CIn, Nex, J, g, v, p, M, FF, GG, NGp, NGm, NF, DGp, DGm, DF, u, L, pL, cL, st, L0, pos, w, wst, tst, r, c0, Rts,  
#	Perp, Seg, Pini, newp, LPols, fQ, f, Q, num, den, new, SUB, pord, PARx, PAR, aux, bux, WtC, WpT, Jnew, gnew, kk, kj;
#	R  := PoscoRoot(CartMatrix(X,n));
#	Rv := R.SimpcoRoot(X,n);
#	wt := FundWeight(X,n)[op({seq(i,i=1..n)} minus convert(K,set))];
#	Std  := Array();                                     # initalize Std whose output of phase k is Std[k], which will consist spaces of cod k in std position
#	s    := cat("CascData/",X,n,"/Gen",Y,m,X,n,k,".mpl");
#	Gen  := Read(s);                                     # the already constructed Gen of Phase k
#	s    := cat("CascData/NilpotentData/NO",Y,m,".mpl");
#	NO   := Read(s);
#	CIn  := [seq(nops(NO(j,2)),j=1..RowDimension(NO))];  # Codimensions of the induced spaces
#	new  := [SearchAll(k+1,CIn)];
#	Nex  := Array(1..nops(new),1..7);                    # the Next Cod-Gen Array Gen[k+1] starts with the induced spaces from (Y,m) and is filled in Phase k
#	for j from 1 to nops(new) do                         # the next lines initialize the Nex Array with the induced data
#		J        := NO(new[j],2);
#		g        := NO(new[j],3);
#		v        := CanonWDD(J,g,Y,m,K,X,n);
#                p        := subs(t=100,seq(x[u]=0,u=1..8),v);
#		M        := PoleSet(v,R);
#                FF       := FFuncNC(v,Y,m,K,X,n);    
#                GG       := GFuncNC(convert(J,list),g,v,Y,m,K,X,n); 
#                NGp      := GG[1][1];
#                NGm      := GG[2][1];
#                NF       := FF[1];
#                DGp      := GG[1][2];
#                DGm      := GG[2][2];
#                DF       := FF[2];
#		Nex(j,1) := M;
#		Nex(j,2) := p;
#		Nex(j,3) := Coord2WDD(CentL(M,X,n),X,n);
#		Nex(j,4) := 0;                               # the pole order of an initial inducing space is 0
#		Nex(j,5) := [NGp,NGm,NF]; 
#		Nex(j,6) := [DGp,DGm,DF]; 
#		Nex(j,7) := [J,g,[]];
#	end do;
#	u := 1;
#	while ( evalb(u <= RowDimension(Gen)) ) do
#		L    := Gen(u,1);
#		pL   := Gen(u,2);
#		cL   := Gen(u,3);
#		pord := Gen(u,4);
#		num  := Gen(u,5);
#		den  := Gen(u,6);
#		pos  := InStdWp(Std,L,Y,m,K,X,n); # Search for an occurrence of (L0,g) in Std such that gL0 is W'-conjugate to L   
#		if ( evalb(nops(pos)>0) ) then
#			# (A) Case when there exists a W'-class for the standard form of L
#			r   := pos[1];                   # r is the row of standard containing the gL0 conjugate to L
#			L0  := Std(r,1);
#			w   := [op(pos[2]),op(Std(r,3)[1])]; # here wL0 = L
#			Seg := Std(r,4);
#			if ( evalb(Std(r,6)=true) ) then
#				# (A1) SUB = true ramification
#				if ( evalb(pL=cL) ) then
#					u := u+1; # if pL=cL in a SUB='true' L0, no movement is needed	
#				else
#					newp := WDDWeyl(pL,Reverse(w),X,n);
#					if ( evalb(newp in {seq(convert(Seg[j][1],list),j=1..nops(Seg))}) ) then
#						# (A1a)
#						u := u+1; # if newp is already an initial point of a SUB='true' L0, the segment [p,c0] needs to be considered only once 
#					else
#						# (A1b)
#						Std(r,3)  := [op(Std(r,3)),w];                 # Modify the Std database by adding the w element that creates the new segment
#						Std(r,4)  := [op(Seg),Array([newp,Std(r,2)])]; # Modify the Std database
#						Std(r,10) := [op(Std(r,10)),L];                # Modify the Std database
#						LPols     := PolesCrossed(L,pL,cL,num,den,X,n); 
#						Nex       := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
#						if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
#							PARx     := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [pL,cL] parallel
#							PAR      := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [pL,cL]
#							Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
#						else
#							PAR := []:
#							Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
#						end if;
#						u := u+1;
#					end if;
#				end if;
#			else
#				# (A2) SUB = false ramification
#				fQ   := DistpPts(pL,{seq(WDDWeyl(convert(Std(r,4)[j][1],list),w,X,n),j=1..nops(Std(r,4)))},Std(r,8),Y,m,K,X,n); 
#				f    := fQ[1];
#				Q    := fQ[2];
#				newp := WDDWeyl(pL,[op(Reverse(w)),op(f)],X,n);
#				if ( evalb(newp in {seq(convert(Seg[j][1],list),j=1..nops(Seg))}) ) then
#					# (A2a)
#					u := u+1; # if newp is already a point of a SUB='false' L0, no movement is needed
#				else
#					# (A2b)
#					Std(r,3)  := [op(Std(r,3)),w]; # Modify the Std database by adding the w element that creates the new segment
#					Std(r,4)  := [op(Seg),Array([newp,WDDWeyl(Q,Reverse(w),X,n)])]; # Modify the Std database and move in a SUB='false' space
#					Std(r,10) := [op(Std(r,10)),L];                                 # Modify the Std database
#					LPols     := PolesCrossed(L,WDDWeyl(pL,f,X,n),Q,num,den,X,n);
#					Nex       := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
#					if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
#						PARx     := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [fpL,Q] parallel
#						PAR      := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [fpL,Q]
#						Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
#					else
#						PAR      := []:
#						Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
#					end if;
#					u := u+1;
#				end if;
#			end if;
#		else
#			# (B) if no W'-class exist
#			if ( evalb(nops(Gen(u,7)[3])=0) ) then
#				Jnew := { seq( K[Gen(u,7)[1][i]]  ,i=1..nops(Gen(u,7)[1]))  }; # These lines are just to make sure
#				gnew := Vector(nops(Jnew));                                    # that for 1st generation spaces
#				for i from 1 to nops(Jnew) do                                  # we don't compute automorphisms of
#					kk      := Search(Jnew[i],K);                          # the space in the stdData procedure.
#					kj      := Search(kk,Gen(u,7)[1]);                     # It also gives a better control on
#					gnew[i] := Gen(u,7)[2][kj];                            # the choices of standard data we use.
#				end do;                                                        #
#				st := [[],Jnew,convert(gnew,list)];                            #
#			else                                                                   #
#				st := stdData(L,X,n);                                          #
#			end if;                                                                #
#			w    := Reverse(st[1]);
#			L0   := LWeyl(L,st[1],X,n);
#			c0   := Coord2WDD(CentL(L0,X,n),X,n);
#			Perp := CstAndPerp(L0,X,n)[2];
#			Pini := WDDWeyl(pL,st[1],X,n);
#			SUB  := SUBTag(L0,Std,Y,m,K,X,n); 
#			if ( evalb(SUB=true) ) then
#				# (B1) SUB = true ramification
#				if ( evalb(pL=cL) ) then
#					# (B1a) When the initial point is the center: no movement
#					Seg := [Array([Pini,Pini])]; # If SUB='true' but pL=cL, there is no movement 
#					PAR := [];                   # If there is no movement on L, PAR = []
#					Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
#					u   := u+1;
#				else
#					# (B1b)
#					Seg   := [Array([Pini,c0])];
#					LPols := PolesCrossed(L,pL,cL,num,den,X,n);
#					Nex   := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
#					if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
#						PARx  := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [pL,cL] parallel
#						PAR   := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [pL,cL]
#						Std   := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
#					else
#						PAR := []:
#						Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
#					end if;
#					u := u+1;
#				end if;
#			else
#				# (B2) SUB = false ramification
#				Seg := [Array([Pini,Pini])]; # The first time a SUB='false' space is added to Std, there is no movement 
#				PAR := [];                   # If there is no movement on L, PAR = []
#				Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
#				u   := u+1;
#			end if;
#		end if;
#	end do;
#	return [Std,Nex];
#end proc; # CascPhase

CascPhase := proc(k::integer,Y::symbol,m::integer,K::list,X::symbol,n::integer)
description "Reads the information stored in Genk.mpl and constructs Std(k).mpl and Gen(k+1).mpl. Here k runs from 0 to n-1";
# added to v4: when deciding if a new entry on Std is to be made, make sure that there is not a previous entry which is W'-conjugate to it 
# added to v7: whenever a movement is not needed, whether because the crossing is at the center or because a segment of movement has been already been created, we still keep track of the potential parent.
	uses LinearAlgebra, ListTools;
	local i, j, R, Rv, wt, s, Std, Gen, NO, CIn, Nex, J, g, v, p, M, FF, GG, NGp, NGm, NF, DGp, DGm, DF, u, L, pL, cL, st, L0, pos, w, wst, tst, r, c0, Rts,  
	Perp, Seg, Pini, newp, LPols, fQ, f, Q, num, den, new, SUB, pord, PARx, PAR, aux, bux, WtC, WpT, Jnew, gnew, kk, kj;
	R    := PoscoRoot(CartMatrix(X,n));
	Rv   := R.SimpcoRoot(X,n);
	wt   := FundWeight(X,n)[op({seq(i,i=1..n)} minus convert(K,set))];
	Std  := Array();                                     # initalize Std whose output of phase k is Std[k], which will consist spaces of cod k in std position
	s    := cat("CascData/",X,n,"/v7Gen",Y,m,X,n,k,".mpl");
	Gen  := Read(s);                                     # the already constructed Gen of Phase k
	s    := cat("CascData/NilpotentData/NO",Y,m,".mpl");
	NO   := Read(s);
	CIn  := [seq(nops(NO(j,2)),j=1..RowDimension(NO))];  # Codimensions of the induced spaces
	new  := [SearchAll(k+1,CIn)];
	Nex  := Array(1..nops(new),1..7);                    # the Next Cod-Gen Array Gen[k+1] starts with the induced spaces from (Y,m) and is filled in Phase k
	for j from 1 to nops(new) do                         # the next lines initialize the Nex Array with the induced data
		J        := NO(new[j],2);
		g        := NO(new[j],3);
		v        := CanonWDD(J,g,Y,m,K,X,n);
                p        := subs(t=100,seq(x[u]=0,u=1..8),v);
		M        := PoleSet(v,R);
                FF       := FFuncNC(v,Y,m,K,X,n);    
                GG       := GFuncNC(convert(J,list),g,v,Y,m,K,X,n); 
                NGp      := GG[1][1];
                NGm      := GG[2][1];
                NF       := FF[1];
                DGp      := GG[1][2];
                DGm      := GG[2][2];
                DF       := FF[2];
		Nex(j,1) := M;
		Nex(j,2) := p;
		Nex(j,3) := Coord2WDD(CentL(M,X,n),X,n);
		Nex(j,4) := 0;                               # the pole order of an initial inducing space is 0
		Nex(j,5) := [NGp,NGm,NF]; 
		Nex(j,6) := [DGp,DGm,DF]; 
		Nex(j,7) := [J,g,[]];
	end do;
	u := 1;
	while ( evalb(u <= RowDimension(Gen)) ) do
		L    := Gen(u,1);
		pL   := Gen(u,2);
		cL   := Gen(u,3);
		pord := Gen(u,4);
		num  := Gen(u,5);
		den  := Gen(u,6);
		pos  := InStdWp(Std,L,Y,m,K,X,n); # Search for an occurrence of (L0,g) in Std such that gL0 is W'-conjugate to L   
		if ( evalb(nops(pos)>0) ) then
			# (A) Case when there exists a W'-class for the standard form of L
			r   := pos[1];                   # r is the row of standard containing the gL0 conjugate to L
			L0  := Std(r,1);
			w   := [op(pos[2]),op(Std(r,3)[1])]; # here wL0 = L
			Seg := Std(r,4);
			if ( evalb(Std(r,6)=true) ) then
				# (A1) SUB = true ramification
				if ( evalb(pL=cL) ) then
					# Change made in v7: keep track of the hits in L0 even though this segment [c0,c0] does not create movements
					Std(r,3)  := [op(Std(r,3)),w];                     # Modify the Std database by adding the w element that creates the new segment
					Std(r,4)  := [op(Seg),Array([Std(r,2),Std(r,2)])]; # Modify the Std database
					Std(r,10) := [op(Std(r,10)),L];                    # Modify the Std database
					u := u+1; # if pL=cL in a SUB='true' L0, no movement is needed	
				else
					newp := WDDWeyl(pL,Reverse(w),X,n);
					if ( evalb(newp in {seq(convert(Seg[j][1],list),j=1..nops(Seg))}) ) then
						# (A1a)
						# Change made in v7: keep track of of the hits in L0 even though this segment has been considered already
						Std(r,3)  := [op(Std(r,3)),w];                 # Modify the Std database by adding the w element that creates the new segment
						Std(r,4)  := [op(Seg),Array([newp,Std(r,2)])]; # Modify the Std database
						Std(r,10) := [op(Std(r,10)),L];                # Modify the Std database
						u := u+1; # if newp is already an initial point of a SUB='true' L0, the segment [p,c0] needs to be considered only once 
					else
						# (A1b)
						Std(r,3)  := [op(Std(r,3)),w];                 # Modify the Std database by adding the w element that creates the new segment
						Std(r,4)  := [op(Seg),Array([newp,Std(r,2)])]; # Modify the Std database
						Std(r,10) := [op(Std(r,10)),L];                # Modify the Std database
						LPols     := PolesCrossed(L,pL,cL,num,den,X,n); 
						Nex       := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
						if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
							PARx     := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [pL,cL] parallel
							PAR      := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [pL,cL]
							Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
						else
							PAR := []:
							Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
						end if;
						u := u+1;
					end if;
				end if;
			else
				# (A2) SUB = false ramification
				fQ   := DistpPts(pL,{seq(WDDWeyl(convert(Std(r,4)[j][1],list),w,X,n),j=1..nops(Std(r,4)))},Std(r,8),Y,m,K,X,n); 
				f    := fQ[1];
				Q    := fQ[2];
				newp := WDDWeyl(pL,[op(Reverse(w)),op(f)],X,n);
				if ( evalb(newp in {seq(convert(Seg[j][1],list),j=1..nops(Seg))}) ) then
					# (A2a)
					# Change made in v7: keep track of the parent even though this segment has been considered already
					Std(r,3)  := [op(Std(r,3)),w];                                      # Modify the Std database by adding the w element that creates the new segment
					Std(r,4)  := [op(Seg),Array([newp,WDDWeyl(Q,Reverse(w),X,n)])];     # Modify the Std database
					Std(r,10) := [op(Std(r,10)),L];                                     # Modify the Std database
					u := u+1; # if newp is already a point of a SUB='false' L0, no movement is needed
				else
					# (A2b)
					Std(r,3)  := [op(Std(r,3)),w]; # Modify the Std database by adding the w element that creates the new segment
					Std(r,4)  := [op(Seg),Array([newp,WDDWeyl(Q,Reverse(w),X,n)])]; # Modify the Std database and move in a SUB='false' space
					Std(r,10) := [op(Std(r,10)),L];                                 # Modify the Std database
					LPols     := PolesCrossed(L,WDDWeyl(pL,f,X,n),Q,num,den,X,n);
					Nex       := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
					if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
						PARx     := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [fpL,Q] parallel
						PAR      := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [fpL,Q]
						Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
					else
						PAR      := []:
						Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
					end if;
					u := u+1;
				end if;
			end if;
		else
			# (B) if no W'-class exist
			if ( evalb(nops(Gen(u,7)[3])=0) ) then
				Jnew := { seq( K[Gen(u,7)[1][i]]  ,i=1..nops(Gen(u,7)[1]))  }; # These lines are just to make sure
				gnew := Vector(nops(Jnew));                                    # that for 1st generation spaces
				for i from 1 to nops(Jnew) do                                  # we don't compute automorphisms of
					kk      := Search(Jnew[i],K);                          # the space in the stdData procedure.
					kj      := Search(kk,Gen(u,7)[1]);                     # It also gives a better control on
					gnew[i] := Gen(u,7)[2][kj];                            # the choices of standard data we use.
				end do;                                                        #
				st := [[],Jnew,convert(gnew,list)];                            #
			else                                                                   #
				st := stdData(L,X,n);                                          #
			end if;                                                                #
			w    := Reverse(st[1]);
			L0   := LWeyl(L,st[1],X,n);
			c0   := Coord2WDD(CentL(L0,X,n),X,n);
			Perp := CstAndPerp(L0,X,n)[2];
			Pini := WDDWeyl(pL,st[1],X,n);
			SUB  := SUBTag(L0,Std,Y,m,K,X,n); 
			if ( evalb(SUB=true) ) then
				# (B1) SUB = true ramification
				if ( evalb(pL=cL) ) then
					# (B1a) When the initial point is the center: no movement
					Seg := [Array([Pini,Pini])]; # If SUB='true' but pL=cL, there is no movement 
					PAR := [];                   # If there is no movement on L, PAR = []
					Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
					u   := u+1;
				else
					# (B1b)
					Seg   := [Array([Pini,c0])];
					LPols := PolesCrossed(L,pL,cL,num,den,X,n);
					Nex   := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
					if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
						PARx  := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [pL,cL] parallel
						PAR   := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [pL,cL]
						Std   := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
					else
						PAR := []:
						Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
					end if;
					u := u+1;
				end if;
			else
				# (B2) SUB = false ramification
				Seg := [Array([Pini,Pini])]; # The first time a SUB='false' space is added to Std, there is no movement 
				PAR := [];                   # If there is no movement on L, PAR = []
				Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
				u   := u+1;
			end if;
		end if;
	end do;
	return [Std,Nex];
end proc; # CascPhase

## Added in May 2025: a procedure to consider a 2-step cascade; the input will be a Gen/Std array, rather than the nilpotent orbits of thee (Y,m) subdiagram
#CascPhase2step := proc(k::integer,Y::symbol,m::integer,K::list,X::symbol,n::integer)
#description "Reads the information stored in Genk.mpl and constructs Std(k).mpl and Gen(k+1).mpl. Here k runs from 0 to n-1,
#             the initializer does not use nilpotent orbits of (Y,m); rather it uses the Gen-Output of a previous iteration of the cascade.";
#	uses LinearAlgebra, ListTools;
#	local i, j, R, Rv, wt, s, Std, Gen, NO, CIn, Nex, J, g, v, p, M, FF, GG, NGp, NGm, NF, DGp, DGm, DF, u, L, pL, cL, st, L0, pos, w, wst, tst, r, c0, Rts,  
#	Perp, Seg, Pini, newp, LPols, fQ, f, Q, num, den, new, SUB, pord, PARx, PAR, aux, bux, WtC, WpT, Jnew, gnew, kk, kj;
#	R    := PoscoRoot(CartMatrix(X,n));
#	Rv   := R.SimpcoRoot(X,n);
#	wt   := FundWeight(X,n)[op({seq(i,i=1..n)} minus convert(K,set))];
#	Std  := Array();                                     # initalize Std whose output of phase k is Std[k], which will consist spaces of cod k in std position
#	s    := cat("CascData/",X,n,"/v7Gen",Y,m,X,n,k,".mpl");
#	Gen  := Read(s);                                     # the already constructed Gen of Phase k
#	s    := cat("CascData/NilpotentData/NO",Y,m,".mpl");
#	NO   := Read(s);
#	CIn  := [seq(nops(NO(j,2)),j=1..RowDimension(NO))];  # Codimensions of the induced spaces
#	new  := [SearchAll(k+1,CIn)];
#	Nex  := Array(1..nops(new),1..7);                    # the Next Cod-Gen Array Gen[k+1] starts with the induced spaces from (Y,m) and is filled in Phase k
#	for j from 1 to nops(new) do                         # the next lines initialize the Nex Array with the induced data
#		J        := NO(new[j],2);
#		g        := NO(new[j],3);
#		v        := CanonWDD(J,g,Y,m,K,X,n);
#                p        := subs(t=100,seq(x[u]=0,u=1..8),v);
#		M        := PoleSet(v,R);
#                FF       := FFuncNC(v,Y,m,K,X,n);    
#                GG       := GFuncNC(convert(J,list),g,v,Y,m,K,X,n); 
#                NGp      := GG[1][1];
#                NGm      := GG[2][1];
#                NF       := FF[1];
#                DGp      := GG[1][2];
#                DGm      := GG[2][2];
#                DF       := FF[2];
#		Nex(j,1) := M;
#		Nex(j,2) := p;
#		Nex(j,3) := Coord2WDD(CentL(M,X,n),X,n);
#		Nex(j,4) := 0;                               # the pole order of an initial inducing space is 0
#		Nex(j,5) := [NGp,NGm,NF]; 
#		Nex(j,6) := [DGp,DGm,DF]; 
#		Nex(j,7) := [J,g,[]];
#	end do;
#	u := 1;
#	while ( evalb(u <= RowDimension(Gen)) ) do
#		L    := Gen(u,1);
#		pL   := Gen(u,2);
#		cL   := Gen(u,3);
#		pord := Gen(u,4);
#		num  := Gen(u,5);
#		den  := Gen(u,6);
#		pos  := InStdWp(Std,L,Y,m,K,X,n); # Search for an occurrence of (L0,g) in Std such that gL0 is W'-conjugate to L   
#		if ( evalb(nops(pos)>0) ) then
#			# (A) Case when there exists a W'-class for the standard form of L
#			r   := pos[1];                   # r is the row of standard containing the gL0 conjugate to L
#			L0  := Std(r,1);
#			w   := [op(pos[2]),op(Std(r,3)[1])]; # here wL0 = L
#			Seg := Std(r,4);
#			if ( evalb(Std(r,6)=true) ) then
#				# (A1) SUB = true ramification
#				if ( evalb(pL=cL) ) then
#					# Change made in v7: keep track of the hits in L0 even though this segment [c0,c0] does not create movements
#					Std(r,3)  := [op(Std(r,3)),w];                     # Modify the Std database by adding the w element that creates the new segment
#					Std(r,4)  := [op(Seg),Array([Std(r,2),Std(r,2)])]; # Modify the Std database
#					Std(r,10) := [op(Std(r,10)),L];                    # Modify the Std database
#					u := u+1; # if pL=cL in a SUB='true' L0, no movement is needed	
#				else
#					newp := WDDWeyl(pL,Reverse(w),X,n);
#					if ( evalb(newp in {seq(convert(Seg[j][1],list),j=1..nops(Seg))}) ) then
#						# (A1a)
#						# Change made in v7: keep track of of the hits in L0 even though this segment has been considered already
#						Std(r,3)  := [op(Std(r,3)),w];                 # Modify the Std database by adding the w element that creates the new segment
#						Std(r,4)  := [op(Seg),Array([newp,Std(r,2)])]; # Modify the Std database
#						Std(r,10) := [op(Std(r,10)),L];                # Modify the Std database
#						u := u+1; # if newp is already an initial point of a SUB='true' L0, the segment [p,c0] needs to be considered only once 
#					else
#						# (A1b)
#						Std(r,3)  := [op(Std(r,3)),w];                 # Modify the Std database by adding the w element that creates the new segment
#						Std(r,4)  := [op(Seg),Array([newp,Std(r,2)])]; # Modify the Std database
#						Std(r,10) := [op(Std(r,10)),L];                # Modify the Std database
#						LPols     := PolesCrossed(L,pL,cL,num,den,X,n); 
#						Nex       := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
#						if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
#							PARx     := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [pL,cL] parallel
#							PAR      := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [pL,cL]
#							Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
#						else
#							PAR := []:
#							Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
#						end if;
#						u := u+1;
#					end if;
#				end if;
#			else
#				# (A2) SUB = false ramification
#				fQ   := DistpPts(pL,{seq(WDDWeyl(convert(Std(r,4)[j][1],list),w,X,n),j=1..nops(Std(r,4)))},Std(r,8),Y,m,K,X,n); 
#				f    := fQ[1];
#				Q    := fQ[2];
#				newp := WDDWeyl(pL,[op(Reverse(w)),op(f)],X,n);
#				if ( evalb(newp in {seq(convert(Seg[j][1],list),j=1..nops(Seg))}) ) then
#					# (A2a)
#					# Change made in v7: keep track of the parent even though this segment has been considered already
#					Std(r,3)  := [op(Std(r,3)),w];                                      # Modify the Std database by adding the w element that creates the new segment
#					Std(r,4)  := [op(Seg),Array([newp,WDDWeyl(Q,Reverse(w),X,n)])];     # Modify the Std database
#					Std(r,10) := [op(Std(r,10)),L];                                     # Modify the Std database
#					u := u+1; # if newp is already a point of a SUB='false' L0, no movement is needed
#				else
#					# (A2b)
#					Std(r,3)  := [op(Std(r,3)),w]; # Modify the Std database by adding the w element that creates the new segment
#					Std(r,4)  := [op(Seg),Array([newp,WDDWeyl(Q,Reverse(w),X,n)])]; # Modify the Std database and move in a SUB='false' space
#					Std(r,10) := [op(Std(r,10)),L];                                 # Modify the Std database
#					LPols     := PolesCrossed(L,WDDWeyl(pL,f,X,n),Q,num,den,X,n);
#					Nex       := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
#					if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
#						PARx     := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [fpL,Q] parallel
#						PAR      := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [fpL,Q]
#						Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
#					else
#						PAR      := []:
#						Std(r,9) := [op(Std(r,9)),PAR]; # Modify the Std database
#					end if;
#					u := u+1;
#				end if;
#			end if;
#		else
#			# (B) if no W'-class exist
#			if ( evalb(nops(Gen(u,7)[3])=0) ) then
#				Jnew := { seq( K[Gen(u,7)[1][i]]  ,i=1..nops(Gen(u,7)[1]))  }; # These lines are just to make sure
#				gnew := Vector(nops(Jnew));                                    # that for 1st generation spaces
#				for i from 1 to nops(Jnew) do                                  # we don't compute automorphisms of
#					kk      := Search(Jnew[i],K);                          # the space in the stdData procedure.
#					kj      := Search(kk,Gen(u,7)[1]);                     # It also gives a better control on
#					gnew[i] := Gen(u,7)[2][kj];                            # the choices of standard data we use.
#				end do;                                                        #
#				st := [[],Jnew,convert(gnew,list)];                            #
#			else                                                                   #
#				st := stdData(L,X,n);                                          #
#			end if;                                                                #
#			w    := Reverse(st[1]);
#			L0   := LWeyl(L,st[1],X,n);
#			c0   := Coord2WDD(CentL(L0,X,n),X,n);
#			Perp := CstAndPerp(L0,X,n)[2];
#			Pini := WDDWeyl(pL,st[1],X,n);
#			SUB  := SUBTag(L0,Std,Y,m,K,X,n); 
#			if ( evalb(SUB=true) ) then
#				# (B1) SUB = true ramification
#				if ( evalb(pL=cL) ) then
#					# (B1a) When the initial point is the center: no movement
#					Seg := [Array([Pini,Pini])]; # If SUB='true' but pL=cL, there is no movement 
#					PAR := [];                   # If there is no movement on L, PAR = []
#					Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
#					u   := u+1;
#				else
#					# (B1b)
#					Seg   := [Array([Pini,c0])];
#					LPols := PolesCrossed(L,pL,cL,num,den,X,n);
#					Nex   := add2Gen(Nex,L,Gen(u,7),LPols,Y,m,K,X,n); 
#					if ( evalb(nops(ArrayTools:-Dimensions(LPols))>0) ) then
#						PARx  := [SearchAll(true,[seq(LPols(j,7),j=1..RowDimension(LPols))])]; # Search for non-const denom roots of L with [pL,cL] parallel
#						PAR   := [seq(op(LWeyl({LPols(PARx[j],3)},Reverse(w),X,n)),j=1..nops(PARx))]; # list of all non-const denom roots parallel to [pL,cL]
#						Std   := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
#					else
#						PAR := []:
#						Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
#					end if;
#					u := u+1;
#				end if;
#			else
#				# (B2) SUB = false ramification
#				Seg := [Array([Pini,Pini])]; # The first time a SUB='false' space is added to Std, there is no movement 
#				PAR := [];                   # If there is no movement on L, PAR = []
#				Std := add2Std(Std,[L0,c0,[w],Seg,pord,SUB,[st[2],st[3]],Perp,[PAR],[L]],X,n);
#				u   := u+1;
#			end if;
#		end if;
#	end do;
#	return [Std,Nex];
#end proc; # CascPhase
