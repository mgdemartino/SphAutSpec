#######################################################################################################################
# Conventions:                                                                                                        #
#     1. Let V and V' be the relevant vector spaces where the geometry takes place.                                   #
#     2. We will always input the 'dual root system', or the 'coroot system', that is, we have R' in V'.              #
#     3. So, here, the simple coroots and the positive coroots live in V'.                                            #
#     4. The fundamental weights live in V.                                                                           #
#     5. The q-residual subspaces all live in V.                                                                      #
#     6. We will adhere to the notational conventions of Bourbaki's Planches I-IX.                                    #
#     7. Simple coroots are basis of V' and fundamental weights are basis for V. Operations are wrt these basis.      #
#######################################################################################################################
# Marcelo De Martino, v19 19/07/2021, adapted to F4 and G2 (not just the E-family exceptionals)
# Included the produres: minRcosetSpeed
# Corrected/changed: CrazyWDD (renamed to CanonWDD), rwExpressionJg, CstValsSTD, GenIniPt, RtString, YminXn, YminXnCp, FFunc, FFuncNC, TrvWDD, Ffactor, DminEn, DminEnCp, GFunc, GFuncNC, IscQRes
# Removed: CrazyGen, CrazierGen, CrazierWDD, CrazyTest, CrazierTest, L2GenIniPt, Where, WhereL, WhereOld, WhereLOld, Gather, CrazyIncl, CrazierIncl, FFuncDE, FFuncNCDE, FfactorDE, Filter, RtFilter, GFuncDE, GFuncNCDE, TrvWDDDE, OrtGen, Iteration, CancelWDD, nCstCancel, PoleOrder, ContourShift, ListContourShift, ListCrazyPolesFull, RegHulls
# General idea of this revision: when dealing with (Y,m) in (X,n), also input K, the list that indicates how the smaller subdiagram embeds in the bigger one

QResidual := module()
description "Series of tools to understand quasi-residual spaces";
option package;
export PRf, AllowcoRt, AssocOrbs, AssocOrbsWhich, Canc, CanvRelevnL, CanvRelevnLop, CartMatrix, CentL, Centre, CentWDD, Close2Cent, ConeEq, Coord2WDD, CanonWDD, Cst, CstEq, CstVals, CstValsSTD, DimL, DPtRes, DPtQRes, FindSpRoots, Ffactor, FFunc, FFuncNC, FundWeight, GenIniPt, GenPt, GenSets,  GFunc, GFuncNC, HasRatVals, Height, HullCollapse, HullInter, Inddata, IndOrbs, IndStep, IntersectionPt, IntersectionPtM, IscQRes, IsQRes, IsReg, IsRes, IsWYmConj, JPoscoRoot, JString, LieDual, ListOrbs, ListProd, ListWeyl, lMCR, LWeyl, longElem, MaxSP, MaxSPCoarse, MaxSPRegularize, minLcoset, minRcoset, minRcosetSpeed, MLieDual, MWeyl, nCstWDD, nd, nnp, no, nonRes, np, npnp, nz, Orbit, ParStab,ParWeyl, PoincPoly, PoleEq,  PoleSet, PoleSetN, PoleSetP, PoscoRoot, Prop, QROrbit, quasiRes, quasiRescod, Read, redExp, regDenom, regDenomp, RegEnvCand, RegComps, RegHulls, RelevnL, ResRts, RtNeighbors, RtString, rvwJg, rvwL, Rw, RwNEW, rwExpressionJg, rwExpressionL, SameAssocOrb, SameAssocOrbElem, SetVec, SetWeyl, SimpRefl, SimpcoRoot, SinR, SpecialcoRts, StabJg, StabL, stdData, stdLElem, stdLElemPar, stdWDD, subWeyl, tRelevnL, TrvWDD, TypeE, vWeyl, WDD2Coord, WDDDom, WDDDomPar, WDDDomElem, WDDDomElemPar, WDDRootProd, WDDRefl, WDDWeyl, Weyl, WeylD5E6, WeylElms, WeylElmsfrom2l, WeylElmsUpl, WeylLength, WeylPeel, WeylRed, WeylReversel, WeylReverser, WeylStep, WD5E6Conj, WE6E7Conj, WYmConj, WYmConjCoarse,  WYmHypConj, WYmOrb, WYmOrbCoarse, WYmSort, YminXn, YminXnCp, ZeroSet, ZeroSetL;

        PRf := proc(r::integer,S::set,X::symbol,n::integer)::set;
                uses LinearAlgebra;
                local R, s, rs, p, i, j;
                R  := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
                s  := {seq(Row(R,S[i]),i=1..nops(S))};
                rs := {seq(s[i] - DotProduct(s[i],LieDual(Row(R,r)))*Row(R,r),i=1..nops(S))};
                p  := {};
                for i from 1 to nops(rs) do
                        for j from 1 to RowDimension(R) do
                                if ( evalb(Norm(rs[i]-Row(R,j),2)=0) ) then
                                        p := p union {j};
                                elif ( evalb(Norm(rs[i]+Row(R,j),2)=0) ) then
                                        p := p union {-j};
                                end if;
                        end do;
                end do;
                return p;
        end proc; # Root reflection permutation subprocedure

        AllowcoRt := proc(g::list,x::numeric,X::symbol,n::integer)::set;
                uses LinearAlgebra;
                local Rv, v, N, d, i, Z, Ax, Al, j, y;
                Rv := PoscoRoot(CartMatrix(X,n));
                v  := Vector[row](g);
                N  := RowDimension(Rv);
                d  := [seq(DotProduct(v,Row(Rv,i)),i=1..N)];
                Z  := ZeroSet(g,Rv);
                Ax := {ListTools:-SearchAll(x-1,d)};
                Al := {};
                for i from 1 to nops(Z) do
                        if ( evalb(PRf(Z[i],Ax,X,n)=Ax) ) then
                                Al := Al union {Z[i]};
                        end if;
                end do;
                return {seq(add(Row(Rv.SimpcoRoot(X,n),Al[i])[j]*y[j],j=1..n),i=1..nops(Al))};
        end proc; #AllowcoRt

	AssocOrbsWhich := proc(J::set,X::symbol,n::integer)::set;
	description "returns the representative of J";
		uses ListTools;
		local aorb, j, ind;
		aorb := AssocOrbs(X,n)[1];
		ind  := Search(true,[seq(member(J,aorb[j]),j=1..nops(aorb))]);
		return aorb[ind][1];
	end proc; #AssocOrbsWhich
		
	AssocOrbs := proc(X::symbol,n::integer)::set;
	description "Returns the W(Y,m)-association class of the subset J of D(X,n)";
		uses ListTools;
		local str, m, s, r, o, j, k, orb, ret;
		str := cat("AssocOrbits/",X,n,".mpl");
		m   := Read(str);
		s   := [seq(nops(m(j,4)),j=1..m(-1,1))];
		r   := [SearchAll(0,s)];	
		o   := [];
		for j from 1 to nops(r) do
			orb := {m(r[j],1)};
			k   := r[j]+1;
			if ( k<m(-1,1) ) then
				while ( nops(m(k,4))>0 ) do
					orb := orb union {m(k,1)};
					k   := k+1;
				end do;	
			end if;	
			o := [op(o),orb];
		end do;
		ret    := Vector(2);
		ret[1] := [seq([seq(m(o[j][k],3),k=1..nops(o[j]))],j=1..nops(o))];
		ret[2] := [seq([seq(m(o[j][k],4),k=1..nops(o[j]))],j=1..nops(o))];
		return ret;
	end proc; # AssocOrbs

	Canc := proc(num::list,den::list)::list;
	description "Cancels the simultaneous ocurrences in Num and in Den";
		uses ListTools;
		local NUM, DEN, i, k, val, nulo;
		NUM := num;
		DEN := den;
		for i from 1 to nops(num) do
                        val := ListTools:-Search(num[i],DEN);
                        if ( val>0 ) then
                                DEN := subsop(val=NULL,DEN);
                                NUM := subsop(i=0,NUM);
                        end if;
                end do;	
		nulo := [SearchAll(false,[seq(evalb(NUM[k]=0),k=1..nops(NUM))])];
                NUM  := [seq(NUM[nulo[k]],k=1..nops(nulo))];        
                return [NUM,DEN];
	end proc; # Canc

	CanvRelevnL := proc(L::set,v::list,X::symbol,n::integer)
	description "Let A = |R+ intersection R_vL(1)| and B = |R+ R_vL(0)|. Checks if A \leq B. The relevance is wrt the function c(-vl)";
		uses ListTools;
		local R, M, gp, Co, Cz, Rv, A, B; 
		R  := PoscoRoot(CartMatrix(X,n));
		M  := SetWeyl(L,v,X,n);
		gp := Coord2WDD(GenPt(M,X,n),X,n);
		Co := PoleSetP(gp,R);
		Cz := ZeroSet(gp,R);
		Rv := SinR(R,R);
		A  := Co intersect Rv;
		B  := Cz intersect Rv;
		return evalb( nops(A)<=nops(B) );
	end proc; # CanvRelevnL

	CanvRelevnLop := proc(L::set,v::list,X::symbol,n::integer)
	description "Similar to CanvRelevnL, but the relevance condition is wrt c(vl)";
		uses ListTools;
		local R, M, gp, Cm, Cz, Rv, A, B; 
		R  := PoscoRoot(CartMatrix(X,n));
		M  := SetWeyl(L,v,X,n);
		gp := Coord2WDD(GenPt(M,X,n),X,n);
		Cm := PoleSetN(gp,R);
		Cz := ZeroSet(gp,R);
		Rv := SinR(R,R);
		A  := Co intersect Rv;
		B  := Cz intersect Rv;
		return evalb( nops(A)<=nops(B) );
	end proc; # CanvRelevnL
	
        CartMatrix := proc(X::symbol,n::integer)::Matrix;
        description "Compute the Cartan matrix";
                uses LinearAlgebra;
                local M, S, i, j, m;
                S := SimpcoRoot(X,n);
                M := Matrix();
                m := RowDimension(S);
                for i from 1 to m do
                        for j from 1 to m do
                                M(i,j) := DotProduct(Row(S,i),2*Row(S,j)/(DotProduct(Row(S,j),Row(S,j))));
                        od;
                od;
                return M;
        end proc; # CartMatrix

        CentL := proc(L::set,X::symbol,n::integer)::Vector;
                uses LinearAlgebra, ListTools;
                local m, R, i, l, CST, s, Ba, VL, t, x, c;
                if ( X=A or X=G ) then
                                m := n+1;
                        elif ( X=E ) then
                                m := 8;
                        else
                                m := n;
                end if;
                if ( nops(L)=0 ) then
                        return convert([seq(0,i=1..m)],Vector[row]);
                else
                        R   := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
                        l   := eval(Vector[row]([seq(y[i],i=1..m)]),solve(PoleEq(L,X,n),{seq(y[i],i=1..m)}));
                        CST := convert(Cst(L,X,n),list);
                        s   := SetVec(MLieDual(<Row(R,CST)>));
                        Ba  := Basis({seq(Vector[row](s[i]),i=1..nops(s))}); 
                        VL  := add(x,x in {seq(t[i]*Ba[i], i=1..nops(Ba))});
                        c   := eval(l,solve({seq(VL[i]=l[i],i=1..m)}));
                        return c;
                end if;
        end proc; # CentL
	
        Centre := proc(J::list,g::list,w::list,X::symbol,n::integer)::Vector;
        description "Returns the centre of the quasi residual subspace defined by (J,g,w).";
                uses LinearAlgebra;
                local M, d, c, i;
                M := MatrixInverse(Transpose(SubMatrix(CartMatrix(X,n),J,J))).MLieDual(<Row(SimpcoRoot(X,n),J)>);
                d := convert(foldl(`+`,0,seq(g[i]*Row(M,i) ,i=1..nops(g))),Vector);        
                c := vWeyl(d,w,X,n);
        end proc; # Centre
	
	CentWDD := proc(g::list,X::symbol,n::integer)::list;
		local R, S;
		R := PoscoRoot(CartMatrix(X,n));
		S := PoleSet(g,R);
		return Coord2WDD(CentL(S,X,n),X,n);
	end proc; # CentWDD
    
#	Close2Cent := proc(Col,row)
#	description "Assumes col is the column of PoleYmXn.mpl that contains the info [J,g,rl]; checks it L(row) is crossed near the centre";
#		uses ListTools, LinearAlgebra;
#		local u, d, test, j, aux, nt;
#		u := 0;
#		d := 0;
#		while ( ((row+d)<=RowDimension(Col)) and evalb(Col(row)[1]=Col(row+d)[1] and evalb(Col(row)[2]=Col(row+d)[2])) ) do
#			d := d+1;
#		end do;
#		while ( evalb(Col(row)[1]=Col(row-u)[1] and Col(row)[2]=Col(row-u)[2]) ) do
#			u := u+1;
#		end do;
#		test := Vector(d+u-1);
#		for j from 1 to (d+u-1) do
#			if ( nops(Col(row)[3])=0 ) then
#				test[j] := true;
#			else
#				if ( verify(Col(row)[3],Col(row-u+j)[3],'sublist') ) then
#					if ( Search(Col(row)[3][-1],Col(row-u+j)[3])=nops(Col(row)[3]) ) then
#						test[j] := true;
#					else
#						test[j] := false;
#					end if;
#				else
#					test[j] := false;
#				end if;
#			end if;
#		end do;
#		nt   := nops([SearchAll(true, convert(test,list))]);
#		if ( nt>1 ) then
#			return false;
#		else
#			return true;
#		end if;
#	end proc; # Close2Cent
# The previous test considered only the c-function

	Close2Cent := proc(Dat,row)
	description "Assumes Dat is PoleYmXn.mpl; checks it L(row) is crossed near the centre, meaning if initial pt is epsilon-close to centre";
		if ( nops(Dat(row,2)[2])=0 ) then
			return false;
		else 
			if  evalb( Dat(row,4)=Dat(row,6)) then
				return true;
			else
				return false;
			end if;
		end if;
	end proc; # Close2Cent

        ConeEq := proc(S::set,X::symbol,n::integer)::set;
                uses LinearAlgebra;
                local m, R, Y, x, i;
                if ( X=A or X=G ) then
                        m := n+1;
                elif ( X=E ) then
                        m := 8;
                else
                        m := n;
                end if;
                R := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
                Y := Vector([seq(y[i],i=1..m)]);
                if ( X=A or X=G ) then
                        return {seq(Row(R,convert(S,list)[i]).Y>=0,i=1..nops(S))}union{add(x,x in{seq(Y[i],i=1..m)})=0};
                elif ( X=E and n=6 ) then
                        return {seq(Row(R,convert(S,list)[i]).Y>=0,i=1..nops(S))}union{Y[6]-Y[7]=0,Y[7]+Y[8]=0};
                elif ( X=E and n=7 ) then
                        return {seq(Row(R,convert(S,list)[i]).Y>=0,i=1..nops(S))}union{Y[7]+Y[8]=0};
                else
                        return {seq(Row(R,convert(S,list)[i]).Y>=0,i=1..nops(S))};
                end if;
        end proc; # ConeEq 

        Coord2WDD := proc(v::Vector,X::symbol,n::integer)::list;
        description "Converts from coordinates to WDD";
                uses LinearAlgebra;
                local Om, Rv, g, i;
                Om := FundWeight(X,n);
                Rv := SimpcoRoot(X,n);
                g  := Array(1..n);
                for i from 1 to n do
                        g[i] := DotProduct(v,Row(Rv,i));
                end do;
                return convert(g,list);
        end proc; #Coord2WDD	
	
	# Changed name to CanonWDD
	# Changed input to (J,g,Y,m,K,X,n)
	CanonWDD := proc(J,g::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
	description "returns a WDD in canonical form, as c + x + t\omega, and x is close to zero (in the sense x->0 and t->0 gives the center c)";
	# The inputs are: (Y,m) the max parabolic, (J,g) a nilpotent orbit of (Y,m), K the (ordered) list indicating how (Y,m) sits in (X,n)
		local Cp, cpnd, G, u, ep, gL, R, c, v;
		Cp   := {seq(u,u=1..m)} minus convert(J,set);
		cpnd := op({seq(u,u=1..n)} minus convert(K,set));
		G    := Vector(n):
		for u from 1 to nops(Cp) do 
			G[K[Cp[u]]] := x[u]; 
		end do;
		G[cpnd] := t; 
		ep      := convert(G,list);
		for u from 1 to nops(g) do 
			G[K[J[u]]] := g[u];
		end do;
		gL := convert(G,list);
		R  := PoscoRoot(CartMatrix(X,n));
		c  := Coord2WDD(CentL(PoleSet(gL,R),X,n),X,n);
		v  := c + ep;
		v  := parse(cat(convert(v,string)));
		return v;
	end proc; # CanonWDD

        Cst := proc(L::set,X::symbol,n::integer)::set;
        description "Returns the set of roots which are constant on L";
                uses LinearAlgebra, combinat, ListTools;
                local Rv, R, t, u, d, cst, S, l;
                Rv  := PoscoRoot(CartMatrix(X,n));
                R   := Rv.SimpcoRoot(X,n);
                t   := GenPt(L,X,n);                                                                 
                d   := [seq(LinearAlgebra:-DotProduct(t,Row(R,l)),l=1..RowDimension(R))];
                cst := [SearchAll(true,[seq(type(d[l],numeric),l=1..nops(d))])];
                S   := convert(cst,set);
                return S;
        end proc; # Cst

	CstEq := proc(v::list,X::symbol,n::integer)::list;
	description "given a subspace L of V parametrized by a WDD with variables v, returns the equivalence classes of roots that are constant on L";
		uses LinearAlgebra;
		local R, Rr, i, j, aux, r, Eq;
		R  := PoscoRoot(CartMatrix(X,n));
		Rr := {seq(i,i=1..RowDimension(R))};
		Eq := [];
		while ( nops(Rr)>0 ) do
			i   := Rr[1];
			aux := {i};
			for j from 1 to nops(Rr) do
				if ( type(WDDRootProd(v,Rr[j],X,n)-WDDRootProd(v,i,X,n),numeric) ) then
					aux := aux union{Rr[j]};
				end if;
			end do;	
			Eq := [op(Eq),aux];
			Rr := Rr minus aux;
		end do;
		return Eq;
	end proc; # CstEq

        CstVals := proc(L::set,X::symbol,n::integer)::list;
        description "Returns a list with the constant values of the pos coroots of (X,n) on L";
                uses LinearAlgebra;
                local CST, c, Rv, d, k;
                CST := Cst(L,X,n);
                c   := CentL(L,X,n);
                Rv  := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
                d   := [seq(Row(Rv,CST[k]).Transpose(c),k=1..nops(CST))];
        end proc; # CstVals
	
	CstValsSTD := proc(J,g::list,rl::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
	description "Returns a list with the constant values of L(J,g,rl) when put in standard position";
		uses ListTools;
		local ini, R, aux, i, lp, Lp, w, L;
		ini  := CanonWDD(J,g,Y,m,K,X,n);
		R    := PoscoRoot(CartMatrix(X,n));
		if ( nops(rl)=0 ) then
			aux := {ini};
		else
			aux  := {subs(t=solve(DotProduct(convert(R[rl[1]],list),ini)=1,t),ini)};
			for i from 2 to nops(rl) do
				aux := aux union {subs(solve(DotProduct(convert(R[rl[i]],list),aux[i-1])=1),aux[i-1])};
			end do;
		end if;
		lp     := aux[nops(aux)];
		Lp     := PoleSet(lp,R);
		w      := stdData(Lp,X,n)[1];
		L      := LWeyl(Lp,w,X,n);
		return CstVals(L,X,n);	
	end proc; # CstValsSTD

	DimL := proc(L::set,X::symbol,n::integer)
	description "Returns the dimension of the space L";
		uses LinearAlgebra;
		local R, B, j;
		R := PoscoRoot(CartMatrix(X,n));
		B := Basis( {seq( sign(L[j])*R[abs(L[j])] , j=1..nops(L) )} );
		return (n - nops(B));
	end proc; # DimL	
		
        DPtRes := proc(X::symbol,n::integer)::list;
        description "Returns a list of WDDs corresponding to the dominant res pts";
                local Xs, ns, s, G, k, R, ix;
                Xs := convert(X,string);
                ns := convert(n,string);
                s  := cat("DataBase-Type",Xs,"/DPt",Xs,ns,".mpl"); 
                G  := Read(s);
                R  := PoscoRoot(CartMatrix(X,n));
                ix := [seq(`if`(nd(G[k],R)>0,NULL,k), k=1..nops(G))];
                return G[ix];
        end proc; # DPtRes
        
        DPtQRes := proc(X::symbol,n::integer)::list; 
        description "Returns a list of WDDs corresponding to the dominant qrespts";
                uses LinearAlgebra, ListTools;
                local Rv, L, i, Q, G0, j, v, k, t, s, p, q;
                if ( n<1 ) then
                        return [];
                end if;
                if ( n=1 ) then
                        return [[1]];
                end if;
                if ( X=D ) then
                        if ( n=2 ) then
                                return [[1,1]];
                        elif ( n=3 ) then
                                return [[1,1,1],[0,1,1]];
                        end if;
                end if;
                Rv := PoscoRoot(CartMatrix(X,n)); # positive roots on V' (we input a Rt Syst on V')
                L := [];
                if ( RowDimension(Rv)=0 ) then
                        return L;
                end if; 
                for i from 1 to n do
                        if ( X=A or X=B or X=C ) then
                                Q := ListProd(DPtQRes(A,i-1),DPtQRes(X,n-i)); 
                        elif ( X=D ) then
                                if ( i<n-1 ) then
                                        Q := ListProd(DPtQRes(A,i-1),DPtQRes(X,n-i));         
                                elif ( i=n-1 or i=n ) then
                                        Q := DPtQRes(A,n-1)
                                end if;
                        elif ( X=E ) then
                                if ( i=1 ) then
                                        Q := DPtQRes(D,n-1);
                                elif ( i=2 ) then
                                        Q := DPtQRes(A,n-1);
                                elif ( i=3 ) then
                                        Q := ListProd(DPtQRes(A,1),DPtQRes(A,n-2));
                                elif ( i=4 ) then
                                        Q := ListProd(ListProd(DPtQRes(A,2),DPtQRes(A,1)),DPtQRes(A,n-4));
                                elif ( i=5 ) then # !!!permuted entries!!!
                                        G0 := DPtQRes(A,4);
                                        Q := ListProd([seq(G0[i][convert([[2,4,3]],permlist,4)],i=1..5)],DPtQRes(A,n-5));
                                elif ( i=6 ) then # !!!permuted entries!!!
                                        G0 := DPtQRes(D,5);
                                        Q := ListProd([seq(G0[i][convert([[2,4,3]],permlist,5)],i=1..12)],DPtQRes(A,n-6));
                                elif ( i=7 ) then
                                        Q := ListProd(DPtQRes(E,6),DPtQRes(A,n-7));
                                elif ( i=8 ) then
                                        Q := DPtQRes(E,7);
                                end if;
                        elif ( X=F ) then
                                if ( i=1 ) then
                                        Q := [seq(Reverse(DPtQRes(C,3)[i]),i=1..3)]; # !!!permuted entries!!!
                                elif ( i=2 ) then
                                        Q := ListProd(DPtQRes(A,1),DPtQRes(A,2));   
                                elif ( i=3 ) then
                                        Q := ListProd(DPtQRes(A,2),DPtQRes(A,1)); 
                                elif ( i=4 ) then
                                        Q := DPtQRes(B,3); 
                                end if;
                        elif ( X=G ) then
                                Q := [[1]];   
                        end if; 
                        L := [op(L),op(IndStep(Q,i,Rv))];
                        L := [seq(WDDDom(L[j],X,n),j=1..nops(L))];
                        L := MakeUnique(L);
                        L := remove(x->( nops(PoleSet(x,Rv))-nops(ZeroSet(x,Rv))<n ),L);
                od;
                return L;
        end proc; # DPtQRes
	
	FindSpRoots := proc(S::set,X::symbol,n::integer)
	description "assumes that the set of positive roots of a root subsystem is given and computes the indivisible roots";
		uses LinearAlgebra, ListTools;
		local R, aux, P, Po, rho, j, d, Sp;
		R   := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
		aux := [seq(evalb(S[j]>0),j=1..nops(S))];
		Po  := [SearchAll(true,aux)];
		P   := {seq(S[Po[j]],j=1..nops(Po))};
		rho := `+`(seq(Row(R,P[j]),j=1..nops(P)));
		d   := [seq(LinearAlgebra:-DotProduct(rho,Row(R,P[j])),j=1..nops(P))];
		Sp  := [SearchAll(2,d)];
		return {seq(P[Sp[j]],j=1..nops(Sp))};
	end proc; # FindSpRoots

	Ffactor := proc(v::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
	description "returns the numerator and the denominator of the F-function restricted to L, parametrized as a WDD with variables";
		uses ListTools;
		local Den, Num, F, R, k;
		F   := YminXnCp(Y,m,K,X,n);
		R   := PoscoRoot(CartMatrix(X,n));
		Num := [seq(DotProduct(convert(LinearAlgebra:-Row(R,F[k]),list),v),k=1..nops(F))];
		Den := [seq(DotProduct(convert(LinearAlgebra:-Row(R,F[k]),list),v)-1,k=1..nops(F))];
		return Canc(Num,Den); 
	end proc; # Ffactor

	FFunc := proc(v::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
	description "Returns [NUM,DEN], the numerator and the denominator of (v,-r)/((v,-r)+1) as rows of R(X,n)";
		uses ListTools, LinearAlgebra;
		local R, S, den, num, NUM, DEN, j, val, nulo;
		R   := PoscoRoot(CartMatrix(X,n));
		S   := YminXnCp(Y,m,K,X,n);
		num := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),v),j=1..nops(S))];
		den := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),v)-1,j=1..nops(S))];
		NUM := S;
		DEN := S;
		for j from 1 to nops(S) do
                        val := Search(num[j],den);
			if ( val>0 ) then
				den := subsop(val="-",den);
				DEN := subsop(val=0,DEN);
				NUM := subsop(j=0,NUM);
			end if;
                end do;
		nulo := [SearchAll(false,[seq(evalb(NUM[j]=0),j=1..nops(NUM))])];
                NUM  := [seq(NUM[nulo[j]],j=1..nops(nulo))];
		nulo := [SearchAll(false,[seq(evalb(DEN[j]=0),j=1..nops(DEN))])];
                DEN  := [seq(DEN[nulo[j]],j=1..nops(nulo))];
                return [NUM,DEN];
	end proc; # FFunc	

	FFuncNC := proc(v::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
	description "Similar to FFunc, but only returns the roots which are non-cst on v";
		uses ListTools, LinearAlgebra;
		local R, Phi, aux, aux2, S, den, num, NUM, DEN, j, val, nulo;
		R    := PoscoRoot(CartMatrix(X,n));
		Phi  := YminXnCp(Y,m,K,X,n);
		aux  := [seq(ListTools:-DotProduct(convert(Row(R,Phi[j]),list),v),j=1..nops(Phi))];
		aux2 := [SearchAll(false,[seq(type(aux[j],numeric),j=1..nops(aux))])]; 
		S    := [seq(Phi[aux2[j]],j=1..nops(aux2))];
		num  := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),v),j=1..nops(S))];
		den  := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),v)-1,j=1..nops(S))];
		NUM  := S;
		DEN  := S;
		for j from 1 to nops(S) do
                        val := Search(num[j],den);
			if ( val>0 ) then
				den := subsop(val="-",den);
				DEN := subsop(val=0,DEN);
				NUM := subsop(j=0,NUM);
			end if;
                end do;
		nulo := [SearchAll(false,[seq(evalb(NUM[j]=0),j=1..nops(NUM))])];
                NUM  := [seq(NUM[nulo[j]],j=1..nops(nulo))];
		nulo := [SearchAll(false,[seq(evalb(DEN[j]=0),j=1..nops(DEN))])];
                DEN  := [seq(DEN[nulo[j]],j=1..nops(nulo))];
                return [NUM,DEN];
	end proc; # FFuncNC
        
	FundWeight := proc(X::symbol,n::integer)::Matrix;
        description "Returns a matrix whose rows are the fundamental weights";
                uses LinearAlgebra;
                local W;
                if ( RowDimension(SimpcoRoot(X,n))=0 ) then
                        return Matrix();
                else
                        W := LinearAlgebra:-MatrixInverse(Transpose(CartMatrix(X,n))).MLieDual(SimpcoRoot(X,n));
                end if;
        end proc; # FundWeight

	GenIniPt := proc(J,g::list,rl::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::Vector;
	description "returns a generic point with vars t, x[1],x[2],... for the space L(J,g)[rl] according to the algorithm of intersections";
		uses ListTools;
		local ini, R, aux, lp, i, j;
		ini := CanonWDD(J,g,Y,m,K,X,n);
		R   := PoscoRoot(CartMatrix(X,n));
		if ( nops(rl)=0 ) then
			aux := {ini};
		else
			aux  := [subs(t=solve(DotProduct(convert(R[abs(rl[1])],list),ini)=sign(rl[1]),t),ini)];
			for i from 2 to nops(rl) do
				aux := [op(aux),subs(solve(DotProduct(convert(R[abs(rl[i])],list),aux[i-1])=sign(rl[i]),{seq(x[j],j=1..(n+2))}),aux[i-1])];
				# the generic variables x[1], x[2], ... go up to n+2 for each type A, B, ... in the models used
			end do;
		end if;
		lp := aux[nops(aux)];
		return [seq(simplify(lp[j]),j=1..nops(lp))];
	end proc; # GenIniPt

	GenPt := proc(L::set,X::symbol,n::integer)
        description "Returns a generic vector in the affine space L";        
                uses LinearAlgebra, ListTools;
                local m, t, u, l;
                if ( X=A or X=G ) then
                        m := n+1;
                elif ( X=E ) then
                        m := 8;
                else
                        m := n;
                end if;
                if ( solve(PoleEq(L,X,n),{seq(y[u],u=1..m)})=NULL ) then
                        return Vector([]);
                else
                        t := eval(Vector[row]([seq(y[l],l=1..m)]),solve(PoleEq(L,X,n),{seq(y[u],u=1..m)}));
                end if;
                return t;
        end proc; # GenPt
	
	GenSets := proc(S::set,L::set,X::symbol,n::integer)::set;
	description"Takes as input a set of roots S and a set of pole roots L. Returns what is the set generated from S by adjoining L, meaning all roots of the type s+l";
		local R, G, i, j, sl, r, s;
		R := PoscoRoot(CartMatrix(X,n));
		G := {};
		for i from 1 to nops(S) do
			for j from 1 to nops(L) do
				sl := R[S[i]] + R[L[j]];	
				r  := SinR(convert(sl,Matrix),R);
				if ( nops(r)>0 ) then
					s := r[1];
					G := G union{s};
				end if;
			end do;
		end do;
		return G;
	end proc; # GenSets
		
	GFunc := proc(J::list,g::list,v::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
	description "Returns [[NUMp,DENp],[NUMm,DEMm]], the numerator and the denominator of (v,r)/((v,r)+1) and (v,-r)/((v,-r)+1) as rows of R(X,n)";
		uses ListTools, LinearAlgebra;
		local z, u, R, S, denp, denm, den, nump, numm, num, NUMp, NUMm, DENp, DENm, j, val, nulo;
		z := [seq(x[u],u=1..n)];
		if ( m=5 ) then
			for j from 1 to nops(J) do
				z[6-J[j]+1] := g[j];
			end do;
		else
			for j from 1 to nops(J) do
				z[J[j]] := g[j];
			end do;
		end if;
		S    := convert(convert(nCstWDD(z,X,n),set) minus convert(YminXnCp(Y,m,K,X,n),set),list);
		R    := PoscoRoot(CartMatrix(X,n));
		nump := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),v),j=1..nops(S))];
		numm := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),-v),j=1..nops(S))];
		num  := [op(nump),op(numm)];
		denp := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),v)+1,j=1..nops(S))];
		denm := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),-v)+1,j=1..nops(S))];
		den  := [op(denp),op(denm)];
		NUMp := S;
		NUMm := S;
		DENp := S;
		DENm := S;
		for j from 1 to nops(S) do
                        val := Search(num[j],den);
                        if ( 0<val and val<nops(S)+1 ) then
				den  := subsop(val="-",den);
                                DENp := subsop(val=0,DENp);
                                NUMp := subsop(j=0,NUMp);
			elif ( val>nops(S) ) then
				den  := subsop(val="-",den);
                                DENm := subsop((val-nops(S))=0,DENm);
                                NUMp := subsop(j=0,NUMp);
                        end if;
                end do;
		for j from 1 to nops(S) do
                        val := Search(num[j+nops(S)],den);
                        if ( 0<val and val<nops(S)+1 ) then
				den  := subsop(val="-",den);
                                DENp := subsop(val=0,DENp);
                                NUMm := subsop(j=0,NUMm);
			elif ( val>nops(S) ) then
				den  := subsop(val="-",den);
                                DENm := subsop((val-nops(S))=0,DENm);
                                NUMm := subsop(j=0,NUMm);
                        end if;
                end do;
		nulo := [SearchAll(false,[seq(evalb(NUMp[j]=0),j=1..nops(NUMp))])];
                NUMp := [seq(NUMp[nulo[j]],j=1..nops(nulo))];        
		nulo := [SearchAll(false,[seq(evalb(NUMm[j]=0),j=1..nops(NUMm))])];
                NUMm := [seq(NUMm[nulo[j]],j=1..nops(nulo))];
		nulo := [SearchAll(false,[seq(evalb(DENp[j]=0),j=1..nops(DENp))])];
                DENp := [seq(DENp[nulo[j]],j=1..nops(nulo))];        
		nulo := [SearchAll(false,[seq(evalb(DENm[j]=0),j=1..nops(DENm))])];
                DENm := [seq(DENm[nulo[j]],j=1..nops(nulo))];
                return [[NUMp,DENp],[NUMm,DENm]];
	end proc; # GFunc

	GFuncNC := proc(J::list,g::list,v::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
	description "Similar to GFunc, but only returns the roots which are non-cst on v";
		uses ListTools, LinearAlgebra;
		local z, u, R, Phi, aux, aux2, S, denp, denm, den, nump, numm, num, NUMp, NUMm, DENp, DENm, j, val, nulo;
		z := [seq(x[u],u=1..n)];
		if ( m=5 ) then
			for j from 1 to nops(J) do
				z[6-J[j]+1] := g[j];
			end do;
		else
			for j from 1 to nops(J) do
				z[J[j]] := g[j];
			end do;
		end if;
		Phi  := convert(convert(nCstWDD(z,X,n),set) minus convert(YminXnCp(Y,m,K,X,n),set),list);
		R    := PoscoRoot(CartMatrix(X,n));
		aux  := [seq(ListTools:-DotProduct(convert(Row(R,Phi[j]),list),v),j=1..nops(Phi))];
		aux2 := [SearchAll(false,[seq(type(aux[j],numeric),j=1..nops(aux))])]; 
		S    := [seq(Phi[aux2[j]],j=1..nops(aux2))];
		nump := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),v),j=1..nops(S))];
		numm := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),-v),j=1..nops(S))];
		num  := [op(nump),op(numm)];
		denp := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),v)+1,j=1..nops(S))];
		denm := [seq(ListTools:-DotProduct(convert(Row(R,S[j]),list),-v)+1,j=1..nops(S))];
		den  := [op(denp),op(denm)];
		NUMp := S;
		NUMm := S;
		DENp := S;
		DENm := S;
		for j from 1 to nops(S) do
                        val := Search(num[j],den);
                        if ( 0<val and val<nops(S)+1 ) then
				den  := subsop(val="-",den);
                                DENp := subsop(val=0,DENp);
                                NUMp := subsop(j=0,NUMp);
			elif ( val>nops(S) ) then
				den  := subsop(val="-",den);
                                DENm := subsop((val-nops(S))=0,DENm);
                                NUMp := subsop(j=0,NUMp);
                        end if;
                end do;
		for j from 1 to nops(S) do
                        val := Search(num[j+nops(S)],den);
                        if ( 0<val and val<nops(S)+1 ) then
				den  := subsop(val="-",den);
                                DENp := subsop(val=0,DENp);
                                NUMm := subsop(j=0,NUMm);
			elif ( val>nops(S) ) then
				den  := subsop(val="-",den);
                                DENm := subsop((val-nops(S))=0,DENm);
                                NUMm := subsop(j=0,NUMm);
                        end if;
                end do;
		nulo := [SearchAll(false,[seq(evalb(NUMp[j]=0),j=1..nops(NUMp))])];
                NUMp := [seq(NUMp[nulo[j]],j=1..nops(nulo))];        
		nulo := [SearchAll(false,[seq(evalb(NUMm[j]=0),j=1..nops(NUMm))])];
                NUMm := [seq(NUMm[nulo[j]],j=1..nops(nulo))];
		nulo := [SearchAll(false,[seq(evalb(DENp[j]=0),j=1..nops(DENp))])];
                DENp := [seq(DENp[nulo[j]],j=1..nops(nulo))];        
		nulo := [SearchAll(false,[seq(evalb(DENm[j]=0),j=1..nops(DENm))])];
                DENm := [seq(DENm[nulo[j]],j=1..nops(nulo))];
                return [[NUMp,DENp],[NUMm,DENm]];
	end proc; # GFuncNC
	
	HasRatVals := proc(L::set,X::symbol,n::integer)
	description "given a pole space L, checks if there are constant roots on L with rational values";
		uses ListTools;
		local cv, test, j;
		cv   := CstVals(L,X,n);
		test := [seq(type(cv[j],fraction),j=1..nops(cv))];
		return evalb(nops([SearchAll(true,test)])>0);
	end proc; #HasRatVals

	Height := proc(r::integer,X::symbol,n::integer)::integer;
	description "returns the height of the root r";
		uses LinearAlgebra;
		local R, W, j;
		R := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
		W := FundWeight(X,n);
		return `+`(seq(DotProduct(Row(W,j),Row(R,r)),j=1..n));
	end proc; # Height
	
	HullCollapse := proc(DenH::list)::Vector;
	description "collapses the multiset of denominators so that there is a unique representative for each denom with its multiplicity";
		uses ListTools, LinearAlgebra;
		local denl, dens, ret, den, aux, mult, j, k, u;
		denl := [seq([seq(DenH[j][k][1],k=1..LinearAlgebra:-Dimension(DenH[j]))],j=1..nops(DenH))];
		dens := [seq(convert(denl[j],set),j=1..nops(DenH))];
		ret  := [seq(Vector(nops(dens[j])),j=1..nops(DenH))];
		for j from 1 to nops (DenH) do
			for k from 1 to nops(dens[j]) do
				den       := dens[j][k];
				aux       := [SearchAll(den,denl[j])];
				mult      := `add`(seq(DenH[j][aux[u]][2],u=1..nops(aux)));
				ret[j][k] := [den,mult];	
			end do;
		end do;
		return ret;
	end proc; # HullCollapse
	
	HullInter := proc(DenH::list)::Vector;
	description "computes the intersection of the multisets of denominators on each Hull; assumes the input has a unique representative for each denominator, with its multiplicity";
		uses ListTools, LinearAlgebra;
		local den, denl, dens, ret, aux, mult, j, k;
		denl := [seq([seq(DenH[j][k][1],k=1..Dimension(DenH[j]))],j=1..nops(DenH))];
		dens := `intersect`(seq(convert(denl[j],set),j=1..nops(DenH)));
		ret  := Vector(nops(dens));
		for j from 1 to nops(dens) do
			den  := [seq(Search(dens[j],denl[k]),k=1..nops(DenH))];
			mult := [seq(DenH[k][den[k]][2],k=1..nops(DenH))];
			ret[j] := [dens[j],min(mult)];
		end do;
		return ret;
	end proc; # HullInter

	Inddata := proc(L::set,X::symbol,n::integer)
	description "Given a pole space L, in terms of its roots, computes the induction data (J,g)";
		uses ListTools;
		local genL, gL, w, v, aux, J, g, j;
		genL := Coord2WDD(GenPt(L,X,n),X,n);
		gL   := subs(seq(y[j]=10000000000+1000000000*j,j=1..(n+2)),genL);
		w    := WDDDomElem(gL,X,n);
		v    := WDDWeyl(genL,w,X,n);
		aux  := [seq(type(v[j],numeric),j=1..n)];
		J    := [SearchAll(true,aux)];
		g    := [seq(v[J[j]],j=1..nops(J))];
		return J,g;
	end proc; # Inddata

	IndOrbs := proc(J::list,g::list,Y::symbol,m::integer)::Vector;
	description "Given a induction parameter (J,g), computes the W(Y,m)-orbits before the induction";
		uses ListTools;
		local s, W, v, j, x, L, M, N, ret, l, aux, w, k;
		s   := cat("WeylGroups/W",Y,m,".mpl");
		W   := Read(s);
		v   := [seq(x[j],j=1..m)];
		for j from 1 to nops(g) do
			v[J[j]] := g[j];
		end do;
		L   := PoleSet(v,PoscoRoot(CartMatrix(Y,m)));
		M   := [seq(LWeyl(L,W[j],Y,m),j=1..nops(W))];
		N   := MakeUnique(M);
		ret := Vector(nops(N));
		for j from 1 to nops(N) do
			l      := N[j];
			aux    := [seq(evalb(l=M[k]),k=1..nops(M))];
			w      := [SearchAll(true,aux)];
			ret[j] := [seq(W[w[k]],k=1..nops(w))];
			ret[j] := [l,op(ret[j])];
		end do;
		return ret;
	end proc; # IndOrbs	

        IndStep := proc(W::listlist,i::integer,R::Matrix)::list;
        description "Middle inductive step to DPtQRes";
                uses LinearAlgebra, ListTools;
                local L, n, j, v, k, t, s, p, q;
                L := [];
                for j from 1 to nops(W) do
                        v := convert([op(1 .. i-1, W[j]), 0, op(i .. -1, W[j])], Vector[column]); 
                        n := Dimension(v);
                        for k from 1 to RowDimension(R) do
                                if ( R[k][i]<>0 ) then
                                        t := (1-Row(R,k).v)/R[k][i];
                                        s := (-1-Row(R,k).v)/R[k][i];
                                        p := convert(convert(v,Vector[row])+t*Row(IdentityMatrix(n),i),list);
                                        q := convert(convert(v,Vector[row])+s*Row(IdentityMatrix(n),i),list);
                                        L := [op([op(L),p]),q];
                                end if;
                                L := MakeUnique(L);
                        od;
                od;
                return L;
        end proc; # IndStep

        IntersectionPt := proc(p::list,c::list,r::integer,X::symbol,n::integer)::Vector;
        description "Given two distinct pts (WDDs) in V(X,n) computes the intersection between the segment [p,c] and the hyperplane r=1. p is allowed to be a WDD with generic entries x[u]";
                uses LinearAlgebra; 
                local R, v, s, k, T, Pt, ret;
                R  := PoscoRoot(CartMatrix(X,n));
		v  := [seq((1-s)*p[k]+s*c[k],k=1..n)];
		T  := solve(ListTools:-DotProduct(convert(Row(R,r),list),v)=1,s);
		Pt := subs(s=T,[seq(v[k],k=1..n)]);
		ret    := Vector(1..2);
		ret[1] := Pt;
		ret[2] := T;
		return ret;
        end proc; # IntersectionPt

	IntersectionPtM := proc(p::list,c::list,r::integer,X::symbol,n::integer)::Vector;
        description "Given two distinct pts (WDDs) in V(X,n) computes the intersection between the segment [p,c] and the hyperplane r=-1. p is allowed to be a WDD with generic entries x[u]";
                uses LinearAlgebra; 
                local R, v, s, k, T, Pt, ret;
                R  := PoscoRoot(CartMatrix(X,n));
		v  := [seq((1-s)*p[k]+s*c[k],k=1..n)];
		T  := solve(ListTools:-DotProduct(convert(Row(R,r),list),v)=-1,s);
		Pt := subs(s=T,[seq(v[k],k=1..n)]);
		ret    := Vector(1..2);
		ret[1] := Pt;
		ret[2] := T;
		return ret;
        end proc; # IntersectionPtM

	IscQRes := proc(L::set,Y::symbol,m::integer,K::list,X::symbol,n::integer)
        description "Returns true or false if the intersection of poles is cqres, meaning, it is conjugated to a qres by the lower rank W'--relevant to the Moeglin algeorithm";
                uses LinearAlgebra, ListTools;
                local R, al, x, mn, j, r, d, o, p, np, z, l;
                R  := PoscoRoot(CartMatrix(X,n));
                d  := CstVals(L,X,n);
                z  := nops([SearchAll(0,d)]);
                p  := nops([SearchAll(1,d)]);
		x  := Coord2WDD(GenPt(L,E,n),E,n);
		mn := YminXn(Y,m,K,X,n);
		al := [seq(ListTools:-DotProduct(convert(Row(R,mn[j]),list),x),j=1..nops(mn))];
		np := nops([SearchAll(-1,al)]);
		if ( nops(convert(x,list))=0 ) then
			return ERROR("The intersections definining L is empty");
		else
			l  := {seq(abs(L[j]),j=1..nops(L))};
                	r  := Rank(<Row(R,convert(l,list))>);
		end if;
                return evalb(p + np - z >= r);        
        end proc; # IscQRes

        IsQRes := proc(L::set,X::symbol,n::integer)
        description "Give a set of roots, returns true or false if the intersection of poles is qres or not";
                uses LinearAlgebra, ListTools;
                local l, R, r, c, o, p, z, j;
		l := {seq(abs(L[j]),j=1..nops(L))};
                R := PoscoRoot(CartMatrix(X,n));
                c := CstVals(L,X,n);
                z := nops([SearchAll(0,c)]);
                p := nops([SearchAll(1,c)]);
                r := Rank(<Row(R,convert(l,list))>);
                return evalb(p - z >= r);        
        end proc; # IsQRes

	IsReg := proc(L::set,X::symbol,n::integer)
	description "Give a pole set, returns true no constant value equal to 0 or false otherwise";
                uses ListTools;
		local val, tst;
		val := CstVals(L,X,n);
		tst := Search(0,val);
		if ( tst>0 ) then
			return false;
		else
			return true;
		end if;
	end proc; # IsReg

        IsRes := proc(L::set,X::symbol,n::integer)
        description "Give a set of roots, returns true or false if the intersection of poles is res or not";
                uses LinearAlgebra, ListTools;
                local l, R, r, c, o, p, z, j;
		l := {seq(abs(L[j]),j=1..nops(L))};
                R := PoscoRoot(CartMatrix(X,n));
                c := CstVals(L,X,n);
                z := nops([SearchAll(0,c)]);
                p := nops([SearchAll(1,c)]) + nops([SearchAll(-1,c)]);
                r := Rank(<Row(R,convert(l,list))>);
                return evalb(p - 2*z >= r);        
        end proc; # IsRes
	
	IsWYmConj := proc(L::set,M::set,n::integer)
	description "returns if two spaces are WYm conjugate or not";
		if ( n=6 ) then
			return WD5E6Conj(L,M);
		elif ( n=7 ) then
			return WE6E7Conj(L,M);
		else
			return WYmConj(L,M,E,8);
		end if;
	end proc; # IsWYmConj

	JPoscoRoot := proc(J::list,Ca::Matrix)::Array; 
        description "Returns the root subsyst of R' gen by J and how it enters R'. Ca is Cart Matrix.";
                uses LinearAlgebra, ListTools;
                local S, N, n, U, i, R, l;
                S := PoscoRoot(SubMatrix(Ca,J,J)); 
                N := RowDimension(S);
                n := ColumnDimension(Ca);
                U := Array(1..N,1..n);
                for i from 1 to nops(J) do
                        U[..,[J[i]]] := Column(S,i);
                od;
                U := convert(U,Matrix);
                R := PoscoRoot(Ca);
                l := SinR(U,R);
                return Array(1..1,1..2,{(1,1)=S,(1,2)=l});
        end proc; #JPoscoRoot

        JString := proc(J::list)::list; 
        description "Returns a list with the sizes of the connected strings of J";
                uses ArrayTools;        
                local s, j, k, N, m, i;            
                s := nops(J);
                j := [op(J),0];
                k := 1;
                N := Array([1]);
                for i from 1 to s do
                        if ( j[i+1]-j[i]=1 ) then
                                N[k]:= N[k]+1
                        else
                                k := k+1;
                                N := Concatenate(2,N,Array([1]));
                        end if;
                od; 
                return convert(N[1..-2],list);
        end proc; # JString

	LieDual := proc(v::Vector)::Vector;
	description "Returns the Lie dual vector";
		uses LinearAlgebra;
		local i, w, N;
			w := [];
			N := DotProduct(v,v);
			if ( Norm(v,1)=0 ) then
				return v;
			else
				for i from 1 to numelems(v) do
					w := [op(w),(2*v[i])/N];
			od;
		end if;
		w := convert(w,Vector[row]);
		return w;
	end proc; # LieDual

	ListOrbs := proc(W::listlist,X::symbol,n::integer)::list;
        description "Returns a list with the qres orbits of each entry";
                uses LinearAlgebra, ListTools;
                local L, i, N, Orb, orb;
                if ( nops(W)=0 ) then
                        return [];
                end if;
                L := W;
                i := 1;
                N := nops(W);        
                while ( i<=N ) do
                        Orb := convert(Orbit(L[i],X,n)(..,1),list);
                        Orb := [op(2..,Orb)];
                        orb := nops(Orb);
                        if ( orb>0 ) then
                                L := [op(1..i,L),op(Orb),op(i+1..N,L)];
                                N := N+orb;
                        fi;
                        i := i+orb+1;
                od;
                return L;
        end proc; # ListOrbits
	
        ListProd := proc(li::list,mi::list)::list;
        description "Returns the cartesian product of the lists.";
                local L, i, j;
                if ( nops(li)=0 ) then
                        return mi;
                elif ( nops(mi)=0 ) then
                        return li;
                end if; 
                L := [];
                for i from 1 to nops(li) do
                        for j from 1 to nops(mi) do 
                                L := [op(L), [op(li[i]),op(mi[j])]];
                        od;
                od;
        end proc; # ListProd

	ListWeyl := proc(Ls::list,w::list,X::symbol,n::integer)
	description "applies w to an ordered set of positive roots";
		local j;
		return [seq(op(SetWeyl({Ls[j]},w,X,n)),j=1..nops(Ls))];
	end proc; # ListWeyl
        
	lMCR := proc(X::symbol,n::integer,J::list)::set;
	# corrected so that now we scan a pre-existing list with all the Weyl group elements (02/02/2019)
	description "returns the set of minimal coset representatives for left W_J-cosets: wW_J";
		uses LinearAlgebra, ListTools;
		local st, W, R, s, S, M, j;
		st := cat("WeylGroups/W",X,n,".mpl");
		if ( FileTools:-Exists(st) ) then
			W := Read(st);
		else
			Export(st,WeylElms(X,n));
			W := Read(st);
		end if;
		R := PoscoRoot(CartMatrix(X,n));
		s := JPoscoRoot(J,CartMatrix(X,n))(1,2);
		S := <seq(Row(R,s[j]),j=1..nops(s))>;
		M := {};
		for j from 1 to nops(W) do
			if ( nops(SinR(MWeyl(S,W[j],X,n),R))>0 ) then
				M := M union {W[j]}
			end if;	
		end do;
		return M;
	end proc; # lMCR

	LWeyl := proc(L::set,w::list,X::symbol,n::integer)::set;
	description "conjugates the residual space L = {PoleSet(L)} by w";
		uses LinearAlgebra, ListTools;
		local R, aux, Lp, Lm, Mp, Mm, Np, Nm, j, k, x, nNp, PNp, NNp, nNm, PNm, NNm, Pos, Neg;
		R   := PoscoRoot(CartMatrix(X,n));
		aux := [seq(evalb(L[j]>=0),j=1..nops(L))];
		Lp  := {seq(L[[SearchAll(true,aux)][j]],j=1..nops([SearchAll(true,aux)]))};
		Lm  := {seq(abs(L[[SearchAll(false,aux)][j]]),j=1..nops([SearchAll(false,aux)]))};
		Mp  := <Row(R,convert(Lp,list))>;
		Mm  := -<Row(R,convert(Lm,list))>;
		if ( nops(Lp)>0 ) then 
			Np := MWeyl(Mp,w,X,n);
		else
			Np := Matrix();
		end if;
		if ( nops(Lm)>0 ) then
			Nm := MWeyl(Mm,w,X,n);
		else
			Nm := Matrix();
		end if;
		nNp := {}; # rows with negative roots of Np
		for j from 1 to RowDimension(Np) do
			if ( add(x, x in seq(Row(Np,j)[k],k=1..ColumnDimension(Np)))<0 ) then;	
				nNp := nNp union {j};
			end if;
		end do;
		PNp := <Row(Np,convert({seq(j,j=1..RowDimension(Np))} minus nNp,list))>;
		NNp := <Row(Np,convert(nNp,list))>;
		nNm := {}; # rows with negative roots of Nm
		for j from 1 to RowDimension(Nm) do
			if ( add(x, x in seq(Row(Nm,j)[k],k=1..ColumnDimension(Nm)))<0 ) then;	
				nNm := nNm union {j};
			end if;
		end do;
		PNm := <Row(Nm,convert({seq(j,j=1..RowDimension(Nm))} minus nNm,list))>;
		NNm := <Row(Nm,convert(nNm,list))>;
		Pos := SinR(convert(PNp,Matrix),R) union SinR(convert(PNm,Matrix),R);	
		Neg := SinR(convert(-NNp,Matrix),R) union SinR(convert(-NNm,Matrix),R);
		Neg := {seq(-Neg[j],j=1..nops(Neg))};
		return Pos union Neg;
	end proc; # LWeyl
        
	longElem := proc(X::symbol,n::integer)::list;
	description "Returns the longest element of the Weyl group of type (X,n)";
		uses LinearAlgebra;
		local w, j, R, test;
		R := PoscoRoot(CartMatrix(X,n));
		w := [];
		j := 1;
		while ( j<n+1 ) do
			test := SinR(convert(Weyl(Row(R,j),w,X,n),Matrix),R); # tests is w(r[j])>0
			if ( nops(test)>0 ) then
				w := [op(w),j];
				j := 1;	
			else
				j := j+1;
			end if;
		end do;
		return w;
	end proc; # longElem
	
	MaxSP := proc(x::integer,Cp::set,X::symbol,n::integer)::set;
	description "Searches the return of MaxSP for falses in the regular test, and if so, finds all regular subsets of maximal cardinality";
		uses ListTools;
		local M, T, F, aux, k, j;
		M   := MaxSPCoarse(x,Cp,X,n);
		T   := [seq(IsReg(M[j],X,n),j=1..nops(M))];
		F   := [SearchAll(false,T)];
		if evalb(nops(F)>0) then
			aux := M minus {seq(M[F[j]],j=1..nops(F))};
			for k from 1 to nops(F) do
				aux := aux union MaxSPRegularize(M[F[k]],X,n);	
			end do;
			M := aux;	
		end if;
		return M;
	end proc; # MaxSP

	MaxSPCoarse := proc(x::integer,Cp::set,X::symbol,n::integer)::set;
	description "Returns the set of maximal subsets {M1, M2, ...} such that Mj = {xj1, xj2, ...} with x in Mj and xjk not a neighbor of xjl if l not k";
		local T, j, k;
		T := Cp minus RtNeighbors(x,Cp,X,n);
		if nops(T) = 0 then
			return {{x}};
		else
			return {seq(seq(MaxSPCoarse(T[j],T,X,n)[k] union {x},k=1..nops(MaxSPCoarse(T[j],T,X,n))),j=1..nops(T))};
		end if;
	end proc; # MaxSPCoarse

	MaxSPRegularize := proc(S::set,X::symbol,n::integer)
	description "Given a set S of pole roots which is not regular, finds the biggest cardinality subsets that are regular";
		uses combinat, ListTools;
		local N, test, i, Sub, aux, pos, j;
		N := nops(S);
		i := 1;
		while evalb((N-i)>0) do
			i    := 1:
			Sub  := choose(N,N-i);
			aux  := [seq(IsReg(S[Sub[j]],X,n),j=1..nops(Sub))];	
			pos  := [SearchAll(true,aux)];
			if evalb(nops(pos)>0) then
				return {seq(S[Sub[pos[j]]],j=1..nops(pos))};	
			else
				i := i-1;
			end if;	
		end do;
	end proc; # MaxSPRegularize

	minLcoset := proc(w::list,X::symbol,n::integer,Wp::list)::list;
	description "Returns [d,u] where w = du, u in W' and d is minimal in the coset wW'. Here Wp is a list that indicates how W' fits inside W(X,n)";
		local u, d, i, r;
		u := [];
		d := w;
		i := 1;
		while ( i<=nops(Wp) ) do
			r := op(LWeyl({Wp[i]},d,X,n)); 
			if ( r<0 ) then
				u := [Wp[i],op(u)];
				d := redExp([op(d),Wp[i]],X,n);
				i := 1;
			else
				i := i+1;
			end if;
		end do;
		return [d,u];
	end proc; # minLcoset

	minRcoset := proc(w::list,X::symbol,n::integer,Wp::list)::list;
	description "Returns [u,d] where w = ud, u in W' and d is minimal in the coset W'w. Here Wp is a list that indicates how W' fits inside W(X,n)";
		uses ListTools;
		local u, d, i, r;
		u := [];
		d := w;
		i := 1;
		while ( i<=nops(Wp) ) do
			r := op(LWeyl({Wp[i]},Reverse(d),X,n)); 
			if ( r<0 ) then
				u := [op(u),Wp[i]];
				d := redExp([Wp[i],op(d)],X,n);
				i := 1;
			else
				i := i+1;
			end if;
		end do;
		return [u,d];
	end proc; # minRcoset

	minRcosetSpeed := proc(w::list,X::symbol,n::integer,Wp::list)::list;
	description "Returns [u,d] where w = ud, u in W' and d is minimal in the coset W'w. Here Wp is a list that indicates how W' fits inside W(X,n)";
		uses ListTools;
		local pos, aux, u, d, i, r;
		# find the first occurence of a reflection not in W'
		pos := Search(false,[seq(evalb(member(w[i],Wp)),i=1..nops(w))]);
		if ( evalb(pos>0) ) then
                	aux := minRcoset([seq(w[i],i=pos..nops(w))],X,n,Wp);
			u   := [seq(w[i],i=1..(pos-1)),op(aux[1])];
			d   := aux[2];
		else
			u   := w:
			d   := []:
		end if;
		return [u,d];
	end proc; # minRcoset

        MLieDual := proc(Mv::Matrix)::Matrix;
        description "Returns the Lie dual of each row";
                uses LinearAlgebra;
                local i, A;
                A := [];
                for i from 1 to RowDimension(Mv) do
                        A := [op(A),convert(LieDual(Row(Mv,i)),list)];
                od;
                A := convert(A,Matrix);
                return A;
        end proc; # MLieDual

        MWeyl := proc(Mr::Matrix,w::list,X::symbol,n::integer)::Matrix;
        description "The action of a Weyl group element given in the rex w";
                uses LinearAlgebra, ArrayTools;
                local W, k;
		if ( RowDimension(Mr)=0 ) then
			return Matrix();
		end if;
                W := convert(Mr,Array);
                for k from 1 to RowDimension(Mr) do;
                        W[k] := Weyl(convert(W[k],Vector),w,X,n);
                od;
                return convert(W,Matrix);
        end proc; # MWeyl
	
	nCstWDD := proc(g::list,X::symbol,n::integer)::set;
	description " g parametrizes L. Returns the set of roots which are nonconstant on L";
		uses LinearAlgebra, ListTools;
                local  R, u, d, nc, S;
                R  := PoscoRoot(CartMatrix(X,n));
                d  := [seq(ListTools:-DotProduct(g,convert(Row(R,u),list)),u=1..RowDimension(R))];
                nc := [SearchAll(false,[seq(type(d[u],numeric),u=1..nops(d))])];
                S  := convert(nc,set);
                return S;
	end proc; # nCstWDD	

        nd := proc(g::list,R::Matrix)::integer;
        description "Returns d = z-o, the defect of g; d=0 implies g is residual";
                local d;
                d := nz(g,R)-no(g,R);
                return d;
        end proc; # nd

        nnp := proc(g::list,R::Matrix)::integer;
        description "Returns np, the cardinality of the negative pole set of g";
                local np;
                np := nops(PoleSetN(g,R));
                return np;
        end proc; # nnp

        no := proc(g::list,R::Matrix)::integer;
        description "Returns o = p-z-n, the (q-residual) order of g";
                local o;
                o := np(g,R)-nz(g,R)-nops(g);
                return o;
        end proc; # no

        nonRes := proc(Qc::Array)::Array;
        description "Searches in Q[cod] (return quasiRe)s for the rows in which defect is not 0";
                uses ArrayTools;
                local l, i;
                l := [];
                for i from 2 to NumElems(Qc(()..(),1)) do
                        if ( Qc(i,2)<>0 ) then
                                l := [op(l),i];
                        fi;
                od;
                if ( nops(l)>0 ) then
                        return Qc([l],()..());
                else
                        return convert(Matrix(),Array);
                end if;
        end proc; # PureQRes

        np := proc(g::list,R::Matrix)::integer;
        description "Returns p, the cardinality of the pole set of g";
                local p;
                p := nops(PoleSet(g,R));
                return p;
        end proc; # np
        
        npnp := proc(g::list,R::Matrix)::integer;
        description "Returns p+np, the sum of the cardinalities of the pole and negative pole sets of g";
                local c;
                c := np(g,R)+nnp(g,R);
                return c;
        end proc; # npcp
        
        nz := proc(g::list,R::Matrix)::integer;
        description "Returns z, the cardinality of the zero set of g";
                local z;
                z := nops(ZeroSet(g,R));
                return z;
        end proc; # nz
    
        Orbit := proc(g::list,X::symbol,n::integer)::Array;
        description "Returns all QRes pts in the orbit of g; faster if g dominant.";
                uses LinearAlgebra, ArrayTools, ListTools;        
                local Rv, v, G, i, o, a, j, k, w, p, u;
                Rv:= PoscoRoot(CartMatrix(X,n));
                if ( RowDimension(Rv)=0 ) then
                        return Array(1..1,1..2,{(1,1)=g,(1,2)=[]});
                end if;
                v := WDDDom(g,X,n);
                G := Array(1..1,1..2,{(1,1)=v,(1,2)=[]});
                i := 1;
                o := 1;
                a := 0;
                while ( i<=o ) do
                        for j from 1 to n do
                                if ( add(Weyl(Row(Rv,j),Reverse(G(i,2)),X,n)[k],k=1..n)>0 ) then
                                        if ( G(i,1)[j]<>0 ) then
                                                v := WDDRefl(G(i,1),j,X,n); 
                                                if ( no(v,Rv)>=0 and Rank( <Row(Rv,[seq(abs(PoleSet(v,Rv)),u=1..nops(PoleSet(v,Rv)))])> )=n ) then
                                                        if ( not member(v,G) ) then
                                                                G := Concatenate(1,G,Array(1..1,1..2,{(1,1)=v,(1,2)=[j,op(G(i,2))]}));
                                                                a := a+1;
                                                        end if;
                                                end if;
                                        end if;
                                end if;
                        od;
                        if ( i=o ) then
                                o := o+a;
                                a := 0;
                        end if;
                        i := i+1;
                od;
                return G;
        end proc; # Orbit

	ParStab := proc(J::set,X::symbol,n::integer)::list;
	description "Returns the group that stabilizes the parabolic subsystem R_J. Only for the E family";
		local r0, s, c, aux, bux, R, C, W, G, H, j, t1, t2, t3, t4, t5;
		if ( X=E ) then
			r0 := Read("WeylGroups/HighestRefl/E6.mpl"):
			if ( n=6 ) then
				#### 01. J = {}
				if ( J={} ) then
					return W(X,n);
				end if;
				#### 02. J = {1}
				if ( J={1} ) then
					W := Read("WeylGroups/WA5.mpl");				
					for j from 1 to nops(W) do
						aux[j] := subs({1=a,2=b,3=c,4=d,5=e},W[j]);
					end do;
					G := [seq(aux[j],j=1..nops(W))];
					s[1]:=r0:
					s[2]:=[2]:
					s[3]:=[4]:
					s[4]:=[5]:
					s[5]:=[6]:
					for j from 1 to nops(W) do
						aux[j] := subs({a=op(s[1]),b=op(s[2]),c=op(s[3]),d=op(s[4]),e=op(s[5])},G[j]);
					end do;
					R := [seq(aux[j],j=1..nops(G))];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 03. J = {2,3}
				if ( J={2,3} ) then
					W := Read("WeylGroups/WB3.mpl");				
					for j from 1 to nops(W) do
						aux[j] := subs({1=a,2=b,3=c},W[j]);
					end do;
					G := [seq(aux[j],j=1..nops(W))];					
					s[1]:=[op(subs({a=3,b=4,c=2},subs({1=a,2=b,3=c},longElem(A,3)))),3,2]:
					s[2]:=[5]:
					s[3]:=[6]:
					for j from 1 to nops(W) do
						aux[j] := subs({a=op(s[1]),b=op(s[2]),c=op(s[3])},G[j]);
					end do;
					R := [seq(aux[j],j=1..nops(G))];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 04. J = {1,3}
				if ( J={1,3} ) then
					W := Read("WeylGroups/WA2.mpl");				
					for j from 1 to nops(W) do
						aux[j] := subs({1=a,2=b},W[j]);
					end do;
					G := [seq(aux[j],j=1..nops(W))];
					s[1]:=r0:
					s[2]:=[2]:
					s[3]:=[5]:
					s[4]:=[6]:
					for j from 1 to nops(W) do
						aux[j] := subs({a=op(s[1]),b=op(s[2])},G[j]);
						bux[j] := subs({a=op(s[3]),b=op(s[4])},G[j]);
					end do;
					G  := [seq(aux[j],j=1..nops(W))]:
					H  := [seq(bux[j],j=1..nops(W))]:
					R  := ListProd(G,H);
					t1 :=[op(subs({a=4,b=3,c=1},subs({1=a,2=b,3=c},longElem(A,3)))),op(subs({a=4,b=3},subs({1=a,2=b},longElem(A,2))))]:
					t2 :=[op(subs({a=2,b=4,c=5},subs({1=a,2=b,3=c},longElem(A,3)))),op(subs({a=4,b=5},subs({1=a,2=b},longElem(A,2))))]:
					t3 :=[op(subs({a=3,b=4,c=2},subs({1=a,2=b,3=c},longElem(A,3)))),op(subs({a=2,b=4},subs({1=a,2=b},longElem(A,2))))]:
					t4 :=[op(subs({a=1,b=3,c=4},subs({1=a,2=b,3=c},longElem(A,3)))),op(subs({a=1,b=3},subs({1=a,2=b},longElem(A,2))))]:
					t5 :=[op(subs({a=3,b=4,c=5},subs({1=a,2=b,3=c},longElem(A,3)))),op(subs({a=3,b=4},subs({1=a,2=b},longElem(A,2))))]:
					c  :=[op(t1),op(t3),op(t2),op(t5),op(t4)]:
					C   := [[],c];
					return ListProd(R,C);
				end if;
				#### 05. J = {1,4,6}
				if ( J={1,4,6} ) then
					W := Read("WeylGroups/WA2.mpl");				
					for j from 1 to nops(W) do
						aux[j] := subs({1=a,2=b},W[j]);
					end do;
					G := [seq(aux[j],j=1..nops(W))];					
					s[1]:=r0;
					s[2]:=[op(subs({a=1,b=3,c=4},subs({1=a,2=b,3=c},longElem(A,3)))),6,1,4,6]:
					s[3]:=[1,op(subs({a=4,b=5,c=6},subs({1=a,2=b,3=c},longElem(A,3)))),1,4,6]:	
					for j from 1 to nops(G) do
						aux[j] := subs({a=op(s[2]),b=op(s[3])},G[j]);
					end do;
					G := [seq(aux[j],j=1..nops(G))];
					H := [[],s[1]];
					R := ListProd(G,H);
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 06. J = {1,2,3}
				if ( J={1,2,3} ) then
					W := Read("WeylGroups/WA2.mpl");				
					for j from 1 to nops(W) do
						aux[j] := subs({1=a,2=b},W[j]);
					end do;
					G := [seq(aux[j],j=1..nops(W))];					
					s[1]:=[5];
					s[2]:=[6];
					for j from 1 to nops(G) do
						aux[j] := subs({a=op(s[1]),b=op(s[2])},G[j]);
					end do;
					R := [seq(aux[j],j=1..nops(G))];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 07. J = {2,3,4}
				if ( J={2,3,4} ) then
					W := Read("WeylGroups/WB2.mpl");				
					for j from 1 to nops(W) do
						aux[j] := subs({1=a,2=b},W[j]);
					end do;
					G := [seq(aux[j],j=1..nops(W))];					
					s[1]:=[op(subs({a=3,b=4,c=5,d=2},subs({1=a,2=b,3=c,4=d},longElem(D,4)))),op(subs({a=3,b=4,c=2},subs({1=a,2=b,3=c},longElem(A,3))))]:
					s[2]:=[6]:
					for j from 1 to nops(G) do
						aux[j] := subs({a=op(s[1]),b=op(s[2])},G[j]);
					end do;
					R := [seq(aux[j],j=1..nops(G))];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 08. J = {1,2,3,5}
				if ( J={1,2,3,5} ) then
					s[1]:=[op(subs({a=1,b=3,c=4,d=5,e=2},subs({1=a,2=b,3=c,4=d,5=e},longElem(D,5)))),op(subs({a=1,b=3},subs({1=a,2=b},longElem(A,2)))),2,5]:
					R := [[],s[1]];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 09. J = {1,3,5,6}
				if ( J={1,3,5,6} ) then
					W := Read("WeylGroups/WG2.mpl");				
					for j from 1 to nops(W) do
						aux[j] := subs({1=a,2=b},W[j]);
					end do;
					G := [seq(aux[j],j=1..nops(W))];					
					s[1]:=[op(subs({a=1,b=3,c=4,d=5,e=6},subs({1=a,2=b,3=c,4=d,5=e},longElem(A,5)))),op(subs({a=1,b=3},subs({1=a,2=b},longElem(A,2)))),op(subs({a=5,b=6},subs({1=a,2=b},longElem(A,2))))]:
					s[2]:=[2]:
					for j from 1 to nops(G) do
						aux[j] := subs({a=op(s[1]),b=op(s[2])},G[j]);
					end do;
					R := [seq(aux[j],j=1..nops(G))];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 10. J = {1,3,4,6}
				if ( J={1,3,4,6} ) then
					s[1]:=r0:
					R := [[],s[1]];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 11. J = {1,2,3,4}
				if ( J={1,2,3,4} ) then
					s[1]:=[6]:
					R := [[],s[1]];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 12. J = {2,3,4,5}
                                if ( J={2,3,4, 5} ) then
                                        W := Read("WeylGroups/WA2.mpl");
                                        for j from 1 to nops(W) do
                                                aux[j] := subs({1=a,2=b},W[j]);
                                        end do;
                                        G := [seq(aux[j],j=1..nops(W))];
					s[1]:=[op(subs({a=1,b=3,c=4,d=5,e=2},subs({1=a,2=b,3=c,4=d,5=e},longElem(D,5)))),op(subs({a=3,b=4,c=5,d=2},subs({1=a,2=b,3=c,4=d},longElem(D,4))))]:
					s[2]:=[op(subs({a=6,b=5,c=4,d=3,e=2},subs({1=a,2=b,3=c,4=d,5=e},longElem(D,5)))),op(subs({a=3,b=4,c=5,d=2},subs({1=a,2=b,3=c,4=d},longElem(D,4))))]:
                                        for j from 1 to nops(G) do
                                                aux[j] := subs({a=op(s[1]),b=op(s[2])},G[j]);
                                        end do;
                                        R := [seq(aux[j],j=1..nops(G))];
                                        C := [[]];
                                        return ListProd(R,C);
                                end if;
				#### 13. J = {1,2,3,5,6}
				if ( J={1,2,3,5,6} ) then
					s[1]:=[op(longElem(E,6)),op(subs({a=1,b=3},subs({1=a,2=b},longElem(A,2)))),2,op(subs({a=5,b=6},subs({1=a,2=b},longElem(A,2))))]:
					R := [[],s[1]];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 14. J = {1,2,3,4,6}
				if ( J={1,2,3,4,6} ) then
					return [[]];
				end if;
				#### 15. J = {1,3,4,5,6}
				if ( J={1,3,4,5,6} ) then
					s[1]:=[op(longElem(E,6)),op(subs({a=1,b=3,c=4,d=5,e=6},subs({1=a,2=b,3=c,4=d,5=e},longElem(A,5))))]:
					R := [[],s[1]];
					C := [[]];
					return ListProd(R,C);
				end if;
				#### 16. J = {1,2,3,4,5}
				if ( J={1,2,3,4,5} ) then
					return [[]];
				end if;
				#### 17. J = {1,2,3,4,5,6}
				if ( J={1,2,3,4,5,6} ) then
					return [[]];
				end if;
			elif ( n=7 ) then
				return ERROR("Under construction");
			elif ( n=8 ) then
				return ERROR("Under construction");
			else
				return ERROR("Only E6, E7, E8");	
			end if;
		else
			return ERROR("Only for the E-family");
		end if;
	end proc; # ParStab
	
	ParWeyl := proc(J::set,X::symbol,n::integer)::list;
	description "computes the standard parabolic subgroup of J";
		uses ListTools, FileTools;
		local W, v, o, G, m, l, j, w, z;
		v    := [seq(1,j=1..n)];	
		o    := {v};
		G[0] := {[]};
		m    := 1;
		l    := 1;
		G[l] := {};
		while ( m>0 ) do
			for w from 1 to nops(G[l-1]) do
				for j from 1 to nops(J) do
					z := WDDWeyl(v,[op(J[j]),op(G[l-1][w])],X,n);
					if ( not member(z,o) ) then
						G[l] := G[l] union {[op(J[j]),op(G[l-1][w])]};
						o    := o union {z};
					end if;
				end do;	
			end do;
			m    := nops(G[l]);
			l    := l+1;
			G[l] := {};
		end do;
		G := `union`(seq(G[j],j=0..(l-1))[]);
		return G;
	end proc; # ParWeyl

	PoincPoly := proc(d::list)
	description "Given the list d of degrees, computes the coefficients of the associated Poincare Polynomial";
		local p, j;
		return coeffs(expand(`*`(seq(expand(simplify((t^d[j]-1)/(t-1))),j=1..nops(d)))));
	end proc; # PoincPoly 

        PoleEq := proc(M::set,X::symbol,n::integer)::set;
                uses LinearAlgebra;
                local m, R, Y, L, x, i;
                if ( X=A or X=G ) then
                        m := n+1;
                elif ( X=E ) then
                        m := 8;
                else
                        m := n;
                end if;
                R := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
                Y := Vector([seq(y[i],i=1..m)]);
		L := [seq(abs(M[i]),i=1..nops(M))];
                if ( X=A or X=G ) then
                        return {seq(Row(R,convert(L,list)[i]).Y=M[i]/abs(M[i]),i=1..nops(L))}union{add(x,x in {seq(Y[i],i=1..m)})=0};
                elif ( X=E and n=6 ) then
                        return {seq(Row(R,convert(L,list)[i]).Y=M[i]/abs(M[i]),i=1..nops(L))}union{Y[6]-Y[7]=0,Y[7]+Y[8]=0};
                elif ( X=E and n=7 ) then
                        return {seq(Row(R,convert(L,list)[i]).Y=M[i]/abs(M[i]),i=1..nops(L))}union{Y[7]+Y[8]=0};
                else
                        return {seq(Row(R,convert(L,list)[i]).Y=M[i]/abs(M[i]),i=1..nops(L))};
                end if;
        end proc; # PoleEq

        PoleSet := proc(g::list,R::Matrix)::set; 
        description "Returns the signed set indexing the poles on g";
                local j, k, nps, pps;
		nps := PoleSetN(g,R);
		pps := PoleSetP(g,R);
                return {seq(-nps[j],j=1..nops(nps))} union {seq(pps[j],j=1..nops(pps))};
        end proc; # PoleSet

	PoleSetN := proc(g::list,R::Matrix)::set; 
        description "Returns a set indexing the pos roots that are minus one on g";
                uses LinearAlgebra;
                local d, i, z;
                d := Vector(RowDimension(R));
                for i from 1 to numelems(d) do
                        d[i] := simplify(DotProduct(convert(g,Vector[row]),R[i]));
                od;
                z := {};
                for i from 1 to numelems(d) do
                        if ( d[i]=-1 ) then
                                z := z union {i};
                        end if;
                od;
                return z;
        end proc; # PoleSetN

	PoleSetP := proc(g::list,R::Matrix)::set; 
        description "Returns a set indexing the pos roots that are plus one on g";
                uses LinearAlgebra;
                local d, i, z;
                d := Vector(RowDimension(R));
                for i from 1 to numelems(d) do
                        d[i] := simplify(DotProduct(convert(g,Vector[row]),R[i]));
                od;
                z := {};
                for i from 1 to numelems(d) do
                        if ( d[i]=1 ) then
                                z := z union {i};
                        end if;
                od;
                return z;
        end proc; # PoleSetP

        PoscoRoot := proc(Ca::Matrix)::Matrix;
        description "Returns |R+|-by-n matrix. Rows: coeff of a pos root in simp rts. Ca is Cart Matrix";
                uses LinearAlgebra, ListTools, FileTools;
                local r, h, i, x, j, p, q, R, s, n; 
                if ( RowDimension(Ca)=0 ) then 
                        return Ca;
                end if;
		n := ColumnDimension(Ca);
		if ( n=6 or n=7 or n=8 ) then
			if ( Ca(1,3)=-1 and Determinant(Ca)<=3 ) then
				s  := cat("DataBase-TypeE/PoscoRootE",n,".mpl");
				if ( Exists(s) ) then
					return Read(s);
				end if;
			end if;
		end if;
                r := [seq(convert(IdentityMatrix(n)[i], list), i=1..n)];
                h := 1;
                i := 1;
                while ( i<=nops(r) ) do
                        if ( add(x,x in r[i])=h ) then
                                for j from 1 to n do
                                        p := 0;
                                        while ( member(r[i]-(p+1)*r[j],r) ) do
                                                p := p+1;
                                        od;
                                        q := p-convert(r[i],Vector).Column(Ca,j);
                                        if ( q>0 ) then
                                                r := [op(r),r[i]+r[j]];
                                                r := MakeUnique(r);
                                        end if;
                                od;
                                i := i+1;
                        else
                                h := h+1;
                        end if;
                od;
                R := convert(r,Matrix);
        end proc; # PoscoRoot

	Prop := proc(X::symbol,n::integer,LW::list,A::set,B::set)::set;
	description "LW a list of weyl group elements, A,B a subset of pos roots. Output: w in LW s.t. A in R(w) and B in R(w)c";
		uses ListTools;
		local R, P, ret, j, k, wR, aux, pos, neg, Rw, Rwc;
		R   := PoscoRoot(CartMatrix(X,n));
		P   := convert(SinR(R,R),list);
		ret := {};
		for j from 1 to nops(LW) do
			wR  := ListWeyl(P,LW[j],X,n);
			aux := [seq(evalb(wR[k]<0),k=1..nops(wR))];
			pos := [SearchAll(false,aux)];
			neg := [SearchAll(true,aux)];
			Rw  := {seq(P[pos[k]],k=1..nops(pos))};
			Rwc := {seq(P[neg[k]],k=1..nops(neg))};
			if ( (A subset Rw) and (B subset Rwc) ) then
				ret := ret union {LW[j]};
			end if; 
		end do;	
		return ret;
	end proc; # Prop
	
        QROrbit := proc(J::list,g::list,X::symbol,n::integer)::Array; 
        description "Returns all quasi-residual spaces in the orbit of (J,g) with g J-dominant.";
                uses LinearAlgebra, ArrayTools, ListTools;        
                local Ca, Rv, Rj, Bj, p, P, c, d, G, i, o, a, j, k;
                Ca := CartMatrix(X,n);
                Rv := PoscoRoot(Ca);
                if ( RowDimension(Rv)=0 ) then
                        return Array(1..1,1..3,[[],[],{}]);
                end if;
                Rj := JPoscoRoot(J,Ca)[1,1];
                if ( no(g,Rj)<0 ) then
                        return ERROR("Entry is not quasi-residual");
                fi;
                Bj := <seq(Rv[JPoscoRoot(J,Ca)[1,2][i]],i=1..nops(J))>; # Simple roots of R_J
                p := PoleSet(g,Rj);
                P := {seq(JPoscoRoot(J,Ca)[1,2][p[i]],i=1..nops(p))};
                c := Centre(J,g,[],X,n);
                G := Array(1..1,1..3,[P,[],c]);
                i := 1;
                o := 1;
                a := 0;
                while ( i<=o ) do
                        for j from 1 to n do
                                if ( SetVec(MWeyl(Bj,[j,op(G(i,2))],X,n)) subset SetVec(Rv) ) then
                                        p := G(i,1);
                                        P := SinR(MWeyl(<(seq(Rv[p[k]],k=1..nops(p)))>,[j],X,n),Rv);
                                        d := vWeyl(c,[j,op(G(i,2))],X,n),X,n;
                                        if ( not member(P,convert(convert(G(..,1),list,nested),set)) ) then
                                                G := Concatenate(1,G,Array(1..1,1..3,[P,[j,op(G(i,2))],d]));
                                                a := a+1;
                                        end if;
                                end if;
                        od;
                        if ( i=o ) then
                                o := o+a;
                                a := 0;
                        end if;
                        i := i+1;
                od;
                return G;
        end proc; # QROrbit

        quasiRes := proc(X::symbol,n::integer)::Array; 
        description "Returns all the quasi-residual subspaces of the given geometry.";
                uses LinearAlgebra, ArrayTools, ListTools;
                local PtA, PtB, PtC, PtD, PtE, PtF, PtG, QR, Q, P, d, S, L, Ca, Rv, cod, aJ, i, J, Rj, Bj, s, Ga, j, g, p, c, k, o, a, u, l;
                if ( n>8 ) or ( n<0 ) then
                        return ERROR("Only considering for ranks from 1 to 8.");
                end if;
                QR    := Array(0..n);
                Q     := Array(1..1,1..3,["Pole Set","Defect","Special Roots"]);
                P     := {};
                d     := 0;
                S     := {seq(i,i=1..RowDimension(PoscoRoot(CartMatrix(X,n))))};
                L     := Array(1..3,[P,d,S]);
                Q     := Concatenate(1,Q,L);
                QR[0] := Q;
                Ca    := CartMatrix(X,n); 
                Rv    := PoscoRoot(Ca);
                for cod from 1 to n do
                        Q := Array(1..1,1..3,["Pole Set","Defect","Special Roots"]);
                        aJ := combinat:-choose([seq(i,i=1..n)],cod);
                        for i from 1 to nops(aJ) do
                                J := aJ[i];
                                Rj := JPoscoRoot(J,Ca)[1,1];
                                Bj := <seq(Rv[JPoscoRoot(J,Ca)[1,2][i]],i=1..nops(J))>; 
                                s := nops(JString(J)); 
                                # This part of the code chases the right subdiagram according to G and the Q-res of J.
                                if ( X=A ) then
                                        PtA[1] := [[1]];
                                        PtA[2] := [[1, 1]]; 
                                        PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                                        PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                                        PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                                        PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                                        PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                                        PtA[8] := Read("DataBase-TypeA/PtA8.mpl");
                                        Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s));
                                elif ( X=B ) then
                                        PtA[1] := [[1]];
                                        PtA[2] := [[1, 1]]; 
                                        PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                                        PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                                        PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                                        PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                                        PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                                        PtB[1] := [[1]];
                                        PtB[2] := [[1, 1], [1, 0]];
                                        PtB[3] := Read("DataBase-TypeB/PtB3.mpl");
                                        PtB[4] := Read("DataBase-TypeB/PtB4.mpl");
                                        PtB[5] := Read("DataBase-TypeB/PtB5.mpl");
                                        PtB[6] := Read("DataBase-TypeB/PtB6.mpl");
                                        PtB[7] := Read("DataBase-TypeB/PtB7.mpl"); 
                                        PtB[8] := Read("DataBase-TypeB/PtB8.mpl"); # needs to be computed
                                        if ( member(n,J) ) then
                                                Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s-1),PtB[JString(J)[s]]);
                                        else
                                                Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s));                
                                        end if;
                                elif ( X=C ) then
                                        PtA[1] := [[1]];
                                        PtA[2] := [[1, 1]]; 
                                        PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                                        PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                                        PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                                        PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                                        PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                                        PtC[1] := [[1]];
                                        PtC[2] := [[1, 1], [0, 1]];
                                        PtC[3] := Read("DataBase-TypeC/PtC3.mpl");
                                        PtC[4] := Read("DataBase-TypeC/PtC4.mpl");
                                        PtC[5] := Read("DataBase-TypeC/PtC5.mpl");
                                        PtC[6] := Read("DataBase-TypeC/PtC6.mpl");
                                        PtC[7] := Read("DataBase-TypeC/PtC7.mpl"); 
                                        PtC[8] := Read("DataBase-TypeC/PtC8.mpl"); # needs to be computed
                                        if ( member(n,J) ) then
                                                Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s-1),PtC[JString(J)[s]]);
                                        else
                                                Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s));                
                                        end if;
                                elif ( X=D ) then
                                        PtA[1] := [[1]];
                                        PtA[2] := [[1, 1]]; 
                                        PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                                        PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                                        PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                                        PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                                        PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                                        PtD[2] := [[1,1]];
                                        PtD[3] := [[1, 1, 1], [0, 1, 1]];  
                                        PtD[4] := Read("DataBase-TypeD/PtD4.mpl");
                                        PtD[5] := Read("DataBase-TypeD/PtD5.mpl");
                                        PtD[6] := Read("DataBase-TypeD/PtD6.mpl");
                                        PtD[7] := Read("DataBase-TypeD/PtD7.mpl"); 
                                        PtD[8] := Read("DataBase-TypeD/PtD8.mpl"); # needs to be computed
                                        if ( {n-1,n} subset convert(J,set) ) then
                                                Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s-1),PtD[JString(J)[s]]);
                                        elif ( member(n-1,J) ) then
                                                Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s)); 
                                        elif ( member(n,J) ) then
                                                s := nops(JString([op(J[1..-2]),n-1]));
                                                Ga := foldl(ListProd,seq(PtA[JString([op(J[1..-2]),n-1])[j]],j=1..s)); 
                                        else
                                                Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s)); 
                                        end if;
                                elif ( X=E ) then
                                        Ga := TypeE(J);
                                elif ( X=F ) then
                                        PtA[1] := [[1]];
                                        PtA[2] := [[1, 1]];
                                        PtB[2] := [[1, 1], [1, 0]]; 
                                        PtB[3] := Read("DataBase-TypeB/PtB3.mpl");
                                        PtC[3] := Read("DataBase-TypeC/PtC3.mpl");
                                        PtF[4] := Read("DataBase-TypeF/PtF4.mpl");
                                        if ( nops(J)=1 ) then
                                                Ga := PtA[1];
                                        elif ( nops(J)=2 ) then
                                                if ( nops(JString(J))=1 ) then
                                                        if ( J=[2,3] ) then
                                                                Ga := PtB[2];
                                                        else
                                                                Ga := PtA[2];
                                                        end if;
                                                else
                                                        Ga := ListProd(PtA[1],PtA[1]);
                                                end if;
                                        elif ( nops(J)=3 ) then
                                                if ( J=[1,2,3] ) then
                                                        Ga := PtB[3];
                                                elif ( J=[1,2,4] ) then
                                                        Ga := ListProd(PtA[2],PtA[1]);
                                                elif ( J=[1,3,4] ) then
                                                        Ga := ListProd(PtA[1],PtA[2]);
                                                elif ( J=[2,3,4] ) then
                                                        Ga := Reverse(PtC[3]);
                                                end if;
                                        else
                                                Ga := PtF[4];
                                        end if;
                                elif ( X=G ) then
                                        PtA[1] := [[1]];
                                        PtG[2] := Read("DataBase-TypeG/PtG2.mpl");
                                        if ( nops(J)=1 ) then
                                                Ga := PtA[1];
                                        else
                                                Ga := PtG[2];
                                        end if;
                                end if;
                                # From now on, we have already the lists of q-res pts of all possible lower ranks.
                                for j from 1 to nops(Ga) do
                                        g := Ga[j];
                                        d := nd(Ga[j],Rj);
                                        p := PoleSet(g,Rj);
                                        P := {seq(JPoscoRoot(J,Ca)[1,2][p[i]],i=1..nops(p))};
                                        c := Centre(J,g,[],X,n);
                                        S := SpecialcoRts(c,X,n);
                                        L := Array(1..1,1..2,[P,[]]);
                                        if ( not member(P,convert(convert(Q(..,1),list,nested),set)) ) then
                                                Q := Concatenate(1,Q,Array([P,d,S]));
                                        end if;
                                        k := 1;
                                        o := 1;
                                        a := 0;
                                        while ( k<=o ) do
                                                for u from 1 to n do
                                                        if ( SetVec(MWeyl(Bj,[u,op(L(k,2))],X,n)) subset SetVec(Rv) ) then
                                                                p := L(k,1);
                                                                P := SinR(MWeyl(<(seq(Rv[p[l]],l=1..nops(p)))>,[u],X,n),Rv);
                                                                S := SpecialcoRts(vWeyl(c,[u,op(L(k,2))],X,n),X,n);
                                                                if ( not member(P,convert(convert(Q(..,1),list,nested),set)) ) then
                                                                        L := Concatenate(1,L,Array(1..1,1..2,[P,[u,op(L(k,2))]]));
                                                                        Q := Concatenate(1,Q,Array(1..1,1..3,[P,d,S]));
                                                                        a := a+1;
                                                                end if;
                                                        end if;
                                                od;
                                                if ( k=o ) then
                                                        o := o+a;
                                                        a := 0;
                                                end if;
                                                k := k+1;
                                        od;
                                od;
                        od;    
                        QR[cod] := Q;
                od;
                return QR;
        end proc; # quasiRes

        quasiRescod := proc(cod::integer,X::symbol,n::integer)::Array; 
        description "Returns all the quasi-residual subspaces of codimension cod in the given geometry.";
                uses LinearAlgebra, ArrayTools, ListTools;
                local PtA, PtB, PtC, PtD, PtE, PtF, PtG, Q, P, d, S, L, Ca, Rv, aJ, i, J, Rj, Bj, s, Ga, j, g, p, c, k, o, a, u, l;
                if ( n>8 ) or ( n<0 ) then
                        return ERROR("Only considering for ranks from 1 to 8.");
                end if;
                Ca := CartMatrix(X,n); 
                Rv := PoscoRoot(Ca);
                if ( cod=0 ) then
                        Q     := Array(1..1,1..3,["Pole Set","Defect","Special Roots"]);
                        P     := {};
                        d     := 0;
                        S     := {seq(i,i=1..RowDimension(Rv))};
                        L     := Array(1..3,[P,d,S]);
                        return Concatenate(1,Q,L);
                end if;
                Q := Array(1..1,1..3,["Pole Set","Defect","Special Roots"]);
                aJ := combinat:-choose([seq(i,i=1..n)],cod);
                for i from 1 to nops(aJ) do
                        J := aJ[i];
                        Rj := JPoscoRoot(J,Ca)[1,1];
                        Bj := <seq(Rv[JPoscoRoot(J,Ca)[1,2][i]],i=1..nops(J))>; 
                        s := nops(JString(J)); 
                        # This part of the code chases the right subdiagram according to G and the Q-res of J.
                        if ( X=A ) then
                                PtA[1] := [[1]];
                                PtA[2] := [[1, 1]]; 
                                PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                                PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                                PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                                PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                                PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                                PtA[8] := Read("DataBase-TypeA/PtA8.mpl");
                                Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s));
                        elif ( X=B ) then
                                PtA[1] := [[1]];
                                PtA[2] := [[1, 1]]; 
                                PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                                PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                                PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                                PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                                PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                                PtB[1] := [[1]];
                                PtB[2] := [[1, 1], [1, 0]];
                                PtB[3] := Read("DataBase-TypeB/PtB3.mpl");
                                PtB[4] := Read("DataBase-TypeB/PtB4.mpl");
                                PtB[5] := Read("DataBase-TypeB/PtB5.mpl");
                                PtB[6] := Read("DataBase-TypeB/PtB6.mpl");
                                PtB[7] := Read("DataBase-TypeB/PtB7.mpl"); 
                                PtB[8] := Read("DataBase-TypeB/PtB8.mpl"); # needs to be computed
                                if ( member(n,J) ) then
                                        Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s-1),PtB[JString(J)[s]]);
                                else
                                        Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s));                
                                end if;
                        elif ( X=C ) then
                                PtA[1] := [[1]];
                                PtA[2] := [[1, 1]]; 
                                PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                                PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                                PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                                PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                                PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                                PtC[1] := [[1]];
                                PtC[2] := [[1, 1], [0, 1]];
                                PtC[3] := Read("DataBase-TypeC/PtC3.mpl");
                                PtC[4] := Read("DataBase-TypeC/PtC4.mpl");
                                PtC[5] := Read("DataBase-TypeC/PtC5.mpl");
                                PtC[6] := Read("DataBase-TypeC/PtC6.mpl");
                                PtC[7] := Read("DataBase-TypeC/PtC7.mpl"); 
                                PtC[8] := Read("DataBase-TypeC/PtC8.mpl"); # needs to be computed
                                if ( member(n,J) ) then
                                        Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s-1),PtC[JString(J)[s]]);
                                else
                                        Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s));                
                                end if;
                        elif ( X=D ) then
                                PtA[1] := [[1]];
                                PtA[2] := [[1, 1]]; 
                                PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                                PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                                PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                                PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                                PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                                PtD[2] := [[1,1]];
                                PtD[3] := [[1, 1, 1], [0, 1, 1]];  
                                PtD[4] := Read("DataBase-TypeD/PtD4.mpl");
                                PtD[5] := Read("DataBase-TypeD/PtD5.mpl");
                                PtD[6] := Read("DataBase-TypeD/PtD6.mpl");
                                PtD[7] := Read("DataBase-TypeD/PtD7.mpl"); 
                                PtD[8] := Read("DataBase-TypeD/PtD8.mpl"); # needs to be computed
                                if ( {n-1,n} subset convert(J,set) ) then
                                        Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s-1),PtD[JString(J)[s]]);
                                elif ( member(n-1,J) ) then
                                        Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s)); 
                                elif ( member(n,J) ) then
                                        s := nops(JString([op(J[1..-2]),n-1]));
                                        Ga := foldl(ListProd,seq(PtA[JString([op(J[1..-2]),n-1])[j]],j=1..s)); 
                                else
                                        Ga := foldl(ListProd,seq(PtA[JString(J)[j]],j=1..s)); 
                                end if;
                        elif ( X=E ) then
                                Ga := TypeE(J);
                        elif ( X=F ) then
                                PtA[1] := [[1]];
                                PtA[2] := [[1, 1]];
                                PtB[2] := [[1, 1], [1, 0]]; 
                                PtB[3] := Read("DataBase-TypeB/PtB3.mpl");
                                PtC[3] := Read("DataBase-TypeC/PtC3.mpl");
                                PtF[4] := Read("DataBase-TypeF/PtF4.mpl");
                                if ( nops(J)=1 ) then
                                        Ga := PtA[1];
                                elif ( nops(J)=2 ) then
                                        if ( nops(JString(J))=1 ) then
                                                if ( J=[2,3] ) then
                                                        Ga := PtB[2];
                                                else
                                                        Ga := PtA[2];
                                                end if;
                                        else
                                                Ga := ListProd(PtA[1],PtA[1]);
                                        end if;
                                elif ( nops(J)=3 ) then
                                        if ( J=[1,2,3] ) then
                                                Ga := PtB[3];
                                        elif ( J=[1,2,4] ) then
                                                Ga := ListProd(PtA[2],PtA[1]);
                                        elif ( J=[1,3,4] ) then
                                                Ga := ListProd(PtA[1],PtA[2]);
                                        elif ( J=[2,3,4] ) then
                                                Ga := Reverse(PtC[3]);
                                        end if;
                                else
                                        Ga := PtF[4];
                                end if;
                        elif ( X=G ) then
                                PtA[1] := [[1]];
                                PtG[2] := Read("DataBase-TypeG/PtG2.mpl");
                                if ( nops(J)=1 ) then
                                        Ga := PtA[1];
                                else
                                        Ga := PtG[2];
                                end if;
                        end if;
                        # From now on, we have already the lists of q-res pts of all possible lower ranks.
                        for j from 1 to nops(Ga) do
                                g := Ga[j];
                                d := nd(Ga[j],Rj);
                                p := PoleSet(g,Rj);
                                P := {seq(JPoscoRoot(J,Ca)[1,2][p[i]],i=1..nops(p))};
                                c := Centre(J,g,[],X,n);
                                S := SpecialcoRts(c,X,n);
                                L := Array(1..1,1..2,[P,[]]);
                                if ( not member(P,convert(convert(Q(..,1),list,nested),set)) ) then
                                        Q := Concatenate(1,Q,Array([P,d,S]));
                                end if;
                                k := 1;
                                o := 1;
                                a := 0;
                                while ( k<=o ) do
                                        for u from 1 to n do
                                                if ( SetVec(MWeyl(Bj,[u,op(L(k,2))],X,n)) subset SetVec(Rv) ) then
                                                        p := L(k,1);
                                                        P := SinR(MWeyl(<(seq(Rv[p[l]],l=1..nops(p)))>,[u],X,n),Rv);
                                                        S := SpecialcoRts(vWeyl(c,[u,op(L(k,2))],X,n),X,n);
                                                        if ( not member(P,convert(convert(Q(..,1),list,nested),set)) ) then
                                                                L := Concatenate(1,L,Array(1..1,1..2,[P,[u,op(L(k,2))]]));
                                                                Q := Concatenate(1,Q,Array(1..1,1..3,[P,d,S]));
                                                                a := a+1;
                                                        end if;
                                                end if;
                                        od;
                                        if ( k=o ) then
                                                o := o+a;
                                                a := 0;
                                        end if;
                                        k := k+1;
                                od;
                        od;
                od;    
                return Q;
        end proc; # quasiRescod

        Read := proc(f::string)
        description "Allows to assign to a variable the contents of a file.";
                local ret;
                read f;
                ret := %;
                return ret;
        end proc; # Read
	
	redExp := proc(w::list,X::symbol,n::integer)::list;
	description "returns a reduced expression for the weyl group element w";
		uses ListTools;
		local g, k;
		g := [seq(1,k=1..n)];
		return Reverse(WDDDomElem(WDDWeyl(g,w,X,n),X,n));
	end proc; # redExp
	
	regDenom := proc(L::set,V::set,w::list,X::symbol,n::integer)::list;
	description "Input: L std pole space, V regular Hull in std position, w such that L inside wV | Output: Compute the denominators of the W-sum on V, restricted to L";
		uses ListTools, LinearAlgebra;
		local R, gL, gV, p,  gH, j, sub, Res, jps, i, aux, rts, DenL, DenH;
		R   := PoscoRoot(CartMatrix(X,n));
		gL  := stdWDD(L,X,n);
		gV  := stdWDD(V,X,n);
		p   := nops([SearchAll(false,[seq(type(gV[j],numeric),j=1..n)])]);
		gV  := subs({seq(x[j] = y[j],j=1..p)}, parse(convert(gV,string))); # we give different variables to V to solve for restricting to L
		gH  := WDDWeyl(gV,w,X,n); # H = wV is the regular hull containing L
		sub := solve({seq( gH[j] = gL[j], j=1..n)}, {seq(y[j],j=1..p)});
		Res := ResRts(gV,X,n); # This Matrix computes all the restricted roots on V (std space in the orbit or a regular envelope of L)
		# The vector jps computes the jump vector of the restricted roots on V. 
		# Each entry is the jump of the restricted root in row i of Res, which is the difference in multiplicity between the successive elements in each string.
		# Res is organized by strings, so the values of jps[i] are:
		# 0  : if i is the first entry of a string or if i in a string and mult(i) = mult(i+1),
		# >0 : if i in a string and mult(i) > mult(i+1) -- here mult is the multiplicity of the restricted root,
		# <0 : if i in a string and mult(i) < mult(i+1).
		jps := Vector(RowDimension(Res)); 
		for i to RowDimension(Res) do 
			if not type(Res(i, 1), numeric) then # the first rows of Res are the constant values of roots in V
				if i = RowDimension(Res) then # For the last entry of any string we have jps[i] = mult[i]
					jps[i] := nops(Res(i,2)); 
				elif evalb( Res(i+1,1)-Res(i,1)=1 ) then # this tests if the next row differs from the previous by 1, i.e., if we are or not in the last entry of a string
					jps[i] := nops(Res(i,2))-nops(Res(i+1,2)); 
				else 
					jps[i] := nops(Res(i,2)); 
				end if; 
			end if; 
		end do;
		aux  := [seq(evalb(jps[i]>0),i=1..Dimension(jps))];
		rts  := [SearchAll(true,aux)]; # rts lists all the rows of Res where there is a downward jump in the multiplicity of a restricted root
		DenH := [seq(Res(rts[i], 1) +1,i=1..nops(rts))]; # This lists all the denominators on H, the regular hull of L
		DenL := [seq( subs(sub,DenH[i]) ,i=1..nops(DenH))];
		return DenL;
	end proc; # regDenom

	regDenomp := proc(L::set,d::list,V::set,w::list,X::symbol,n::integer,Wp::list)::list;
        description "Input: L std pole space, d minimal rep in W'dF_L, V regular Hull in std position, w such that L inside wV | Output: Compute the denominators of the W'-sum on V, restricted to L";
	# Wp is W'
                uses ListTools, LinearAlgebra;
                local R, f, Rf, Rp, Rfp, gL, gV, p, gH, j, SUB, Res, Resf, jps, i, aux, rts, DenLp, DenHp;
                R   := PoscoRoot(CartMatrix(X,n));
		f   := minRcoset([op(d),op(w)],X,n,Wp)[2];
		Rf  := Rw(f, X, n);
		Rp  := JPoscoRoot(Wp, CartMatrix(X,n))(1, 2);
		Rfp := LWeyl(Rp, Reverse(f),X,n) union Rf;
                gL  := stdWDD(L,X,n);
                gV  := stdWDD(V,X,n);
                p   := nops([SearchAll(false,[seq(type(gV[j],numeric),j=1..n)])]);
                gV  := subs({seq(x[j] = y[j],j=1..p)}, parse(convert(gV,string))); # we give different variables to V to solve for restricting to L
                gH  := WDDWeyl(gV,w,X,n); # H = wV is the regular hull containing L
                SUB := solve({seq( gH[j] = gL[j], j=1..n)}, {seq(y[j],j=1..p)});
                Res := ResRts(gV,X,n); # This Matrix computes all the restricted roots on V (std space in the orbit or a regular envelope of L)
                # The vector jps computes the jump vector of the restricted roots on V. 
                # Each entry is the jump of the restricted root in row i of Res, which is the difference in multiplicity between the successive elements in each string.
                # Res is organized by strings, so the values of jps[i] are:
                # 0  : if i is the first entry of a string or if i in a string and mult(i) = mult(i+1),
                # >0 : if i in a string and mult(i) > mult(i+1) -- here mult is the multiplicity of the restricted root,
                # <0 : if i in a string and mult(i) < mult(i+1). 
		Resf := Matrix(RowDimension(Res), 2);
		for i to RowDimension(Resf) do 
			Resf(i, 1) := Res(i, 1); 
			Resf(i, 2) := Res(i, 2) intersect Rfp; 
		end do;
                jps  := Vector(RowDimension(Resf)); 
		for i to RowDimension(Resf) do 
			if not type(Resf(i, 1), numeric) then 
				if ( i = 1 ) then 
					jps[i] := nops(Resf(i, 2)); 
				elif evalb(Resf(i, 1)-Resf(i-1, 1) = 1) then 
					jps[i] := nops(Resf(i, 2))-nops(Resf(i-1, 2)); 
				else 
					jps[i] := nops(Resf(i, 2)); 
				end if; 
			end if; 
		end do;
                aux   := [seq(evalb(jps[i]>0),i=1..Dimension(jps))];
                rts   := [SearchAll(true,aux)]; # rts lists all the rows of Resp where there is a downward jump in the multiplicity of a restricted root
                DenHp := [seq(Resf(rts[i], 1),i=1..nops(rts))]; # This lists all the denominators on H, the regular hull of L
                DenLp := [seq(subs( SUB, DenHp[i] ) ,i=1..nops(DenHp))];
                return DenLp;
        end proc; # regDenomp 	
	
	RegEnvCand := proc(L::set,X::symbol,n::integer)
	description "given a pole space L, returns the set of all pole roots p that can be written as p = q + s, with q also a pole root and s a singular root";
		uses ListTools, LinearAlgebra;
		local R, pt, RV, SR, rR, rt, riR, i, j;
		R  := PoscoRoot(CartMatrix(X,n));
		pt := Coord2WDD(GenPt(L,X,n),X,n);
		RV := [seq(DotProduct(convert(R[j],list),pt),j=1..RowDimension(R))];
		SR := {SearchAll(0,RV)};
		rR := {};
		if nops(SR) > 0 then
			for i from 1 to nops(L) do
				for j from 1 to nops(SR) do
					rt  := convert(R[L[i]] + R[SR[j]],Matrix);
					riR := SinR(rt,R);
					if ( nops(riR)>0 ) then
						rR := rR union riR;
					end if;
				end do;	
			end do;
		end if;
		return rR;
	end proc; # RegEnvCand
	
	RegComps := proc(L::set,X::symbol,n::integer)::list;
	description "computes the transitive closure of the symmetric Neighboring relation";
		uses ListTools;
		local R, Comps, temp, Cp, cp, key, i;
		R := PoscoRoot(CartMatrix(X,n));
		Comps := [];
		temp := L;
		while ( nops(temp)>0 ) do
			key := 1;
			Cp := RtNeighbors(temp[1],L,X,n);
			while ( key>0 ) do
				cp := nops(Cp);
				for i from 1 to cp do
					Cp := Cp union RtNeighbors(Cp[i],L,X,n);
				end do;	
				if ( nops(Cp)=cp ) then
					key := 0;
				end if;
			end do;
			Comps := [op(Comps),Cp];
			temp := temp minus Cp;
		end do;
		return Comps;
	end proc; # RegComps

	RegHulls := proc(L::set,X::symbol,n::integer)::list;
	description "returns a set whose entries are regular spaces containing L";
	# Added a line to first search if a regular hull exists before computing
		uses combinat, ListTools, FileTools;
		local Cps, MSp, j, k, T, V, H, aux, st;
		st := cat("CascData/",X,n,"/Hulls/Hall",convert(L,string),".mpl");
		if ( Exists(st) ) then
			return Read(st);
		else
			Cps := RegComps(L,X,n);
			MSp := Vector(nops(Cps));
			for k from 1 to nops(Cps) do
				MSp[k] := {seq(op(MaxSP(Cps[k][j],Cps[k],X,n)),j=1..nops(Cps[k]))};
			end do;
			T := cartprod([seq(MSp[j],j=1..nops(Cps))]);
			H := {};
			while not T[finished] do 
				aux := T[nextvalue]();
				V   := `union`(seq(aux[j],j=1..nops(aux)));
				H   := H union {V};
			end do;
			return H;
		end if;
	end proc; # RegHulls

	RelevnL := proc(L::set,X::symbol,n::integer)::set;
	description "computes the weyl group elements which are relevant (the (*) condition) on a given pole space L";
		uses ListTools, FileTools;
		local st, nam, s, W, test, ret, j, RET;
		st := cat("Relevant/",X,n,"/",L[1]);
		for j from 2 to nops(L) do
			st := cat(st,"_",L[j]);
		end do;
		st := cat(st,".mpl");
		if ( Exists(st) ) then
			return Read(st);
		else
			s    := cat("WeylGroups/W",X,n,".mpl");
			W    := Read(s);
			test := [seq(CanvRelevnL(L,W[j],X,n),j=1..nops(W))];
			ret  := [SearchAll(true,test)];
			RET  := {seq(W[ret[j]],j=1..nops(ret))};
			Export(st,RET);
			return RET;
		end if;
	end proc; # RelevnL

	ResRts := proc(p::list,X::symbol,n::integer)::Matrix;
	description "Given p a generic WDD on a pole space L, returns a vector where each entry is a pair [rr,rrS], rr is the value of a root on p and rrS is the set of all roots with value rr.";
		uses LinearAlgebra, ListTools;
		local R, Res, res, sRR, val, aux, bux, pos, cux, dux, srt, RR, i, rr, rrS, j;
		R   := PoscoRoot(CartMatrix(X,n));
		Res := [seq(ListTools:-DotProduct(p,convert(R[j],list)),j=1..RowDimension(R))];	
		### here we will sort the values of the nonconstant restricted roots as strings
		res := convert(Res,set); 
		sRR := [];
		while nops(res)>0 do
			val := res[1];
			aux := [seq(res[i] - val,i=1..nops(res))];
			bux := [seq(type(aux[i],numeric),i=1..nops(aux))];
			pos := [SearchAll(true,bux)];
			cux := {seq(aux[pos[i]],i=1..nops(pos))};
			dux := [seq(Search(cux[i],aux),i=1..nops(cux))];
			srt := [seq(res[dux[i]],i=1..nops(dux))];
			sRR := [op(sRR),op(srt)];
			res := res minus {seq(res[pos[i]],i=1..nops(pos))};
		end do;
		RR := Matrix(nops(sRR),2);
		for i from 1 to nops(sRR) do
			RR(i,1) := sRR[i];
			RR(i,2) := {SearchAll(RR(i,1),Res)};
		end do;
		return RR;
	end proc; # ResRts	

	RtNeighbors := proc(r::integer,L::set,X::symbol,n::integer)::list;
	description "Given a set of poles L, and r in L, returns the neighborhood of r. Here, s is a neighbor of r if r - s is a root or zero";
		uses ListTools, LinearAlgebra;
		local pR, R, Ns, i, j;
		pR := PoscoRoot(CartMatrix(X,n));
		R  := Matrix(2*RowDimension(pR)+1,ColumnDimension(pR));
		for i from 1 to RowDimension(pR) do
			for j from 1 to ColumnDimension(pR) do
				R(i,j) := pR(i,j);
				R(i+RowDimension(pR),j) := -pR(i,j);
			end do;
		end do;
		Ns := {};
		for i from 1 to nops(L) do
			if ( nops(SinR(convert(pR[r]-pR[L[i]],Matrix),R))>0 ) then
				Ns := Ns union {L[i]};	
			end if;	
		end do;
		return Ns;
	end proc; # RtNeighbors

	RtString := proc(J,g::list,rl::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::Vector;
	description "returns the strings of non constant root values, with multiplicity, on L(J,g,rl) in std position";
		uses ListTools;
		local ini, R, aux, i, lp, Lp, w, L, lambda, nCstRt, nCstm, nCstv, aST, val, bux, pos, cux, srt, STR;
		ini  := CanonWDD(J,g,Y,m,K,X,n);
		R    := PoscoRoot(CartMatrix(X,n));
		if ( nops(rl)=0 ) then
			aux := {ini};
		else
			aux  := {subs(t=solve(DotProduct(convert(R[rl[1]],list),ini)=1,t),ini)};
			for i from 2 to nops(rl) do
				aux := aux union {subs(solve(DotProduct(convert(R[rl[i]],list),aux[i-1])=1),aux[i-1])};
			end do;
		end if;
		lp     := aux[nops(aux)];
		Lp     := PoleSet(lp,R);
		w      := stdData(Lp,X,n)[1];
		L      := LWeyl(Lp,w,X,n);
		lambda := WDDWeyl(lp,w,X,n);
		nCstRt := {seq(i,i=1..LinearAlgebra:-RowDimension(R))} minus Cst(L,X,n);
		nCstm  := [seq(DotProduct(convert(R[nCstRt[i]],list),lambda),i=1..nops(nCstRt))];
		nCstv  := convert(nCstm,set); 
		aST    := {};
		while nops(nCstv)>0 do
			val   := nCstv[1];
			bux   := [seq(type(nCstv[i] - val,numeric),i=1..nops(nCstv))];
			pos   := [SearchAll(true,bux)];
			cux   := [seq(nCstv[pos[i]] - val,i=1..nops(pos))];
			srt   := [seq(Search(convert(cux,set)[i],cux),i=1..nops(cux))];
			aST   := aST union { [seq( [ nCstv[pos[srt[i]]],nops([SearchAll(nCstv[pos[srt[i]]],nCstm)]) ] ,i=1..nops(srt))] };
			nCstv := nCstv minus {seq(nCstv[pos[i]],i=1..nops(pos))};
		end do;
		STR := Vector(nops(aST));
		for i from 1 to nops(aST) do
			STR[i] := aST[i];
		end do;
		return STR;
	end proc; # RtString

	rvwJg := proc(v::list,w::list,J::list,g::list,Y::symbol,m::integer,X::symbol,n::integer)
	description "given Weyl group elements (v,w) computes, module constant factors, the expression r(vl)/v(wl)|L where l is generic in L(J,g)";
		uses ListTools;
		return rwExpressionJg([op(w),op(Reverse(v))],J,g,Y,m,X,n);
	end proc; # rvwL

	rvwL := proc(v::list,w::list,L::set,X::symbol,n::integer)
	description "given Weyl group elements (v,w) computes, module constant factors, the expression r(vl)/v(wl)|L where l is generic in L";
		uses ListTools;
		return rwExpressionL([op(w),op(Reverse(v))],L,X,n);
	end proc; # rvwL

	Rw := proc(w::list,X::symbol,n::integer)::set;
	description "Given a Weyl group element w, returns the set of positive roots made negative by w";
		local j, k:
		return {seq(op(LWeyl({w[-j]},[seq(w[-k],k=1..(j-1))],X,n)),j=1..nops(w))};
	end proc; # Rw

	RwNEW := proc(w::list,X::symbol,n::integer)::set;
        description "Given a Weyl group element w, returns the set of positive roots made negative by w";
                local aux, bux, cux, i, Rt, N;
                Rt  := PoscoRoot(CartMatrix(X,n));
                N   := LinearAlgebra:-RowDimension(Rt);
                aux := [seq(op(LWeyl({i},w,X,n)),i=1..N)];
                bux := [seq(evalb(aux[i]<0),i=1..N)];
                cux := [ListTools:-SearchAll(true,bux)];
                return convert(cux,set);
        end proc; # RwNEW
	
	rwExpressionJg := proc(w::list,J::list,g::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::list; 
	description "computes the (non-cst terms of the) numerator and the denominator of r(l)/r(wl) restricted L(J,g)";
		uses LinearAlgebra, ListTools;
		local R, aux, Rw, gL, nn, var, d, nCi, nC, den, num, j;
		R   := PoscoRoot(CartMatrix(X,n));
		aux := SetVec(R) intersect SetVec(MWeyl(-R,Reverse(w),X,n)); 
		if ( nops(aux)>0 ) then
			Rw := SinR(<seq(convert(aux[j],Vector[row]),j=1..nops(aux))>,R);
		else
			Rw := {};
		end if;
		if ( m<5 or m>7 ) then
			return ERROR("We are only considering E6, E7, E8.");
		else
			gL := CanonWDD(J,g,Y,m,K,X,n);
		end if;
		# nn  := [SearchAll(false,[seq(type(gL[j],numeric),j=1..nops(gL))])];
		# var := [seq(x[j],j=1..nops(nn))];
		# for j from 1 to nops(nn) do
		# 	gL[nn[j]] := var[j];
		# end do;
		d   := [seq(ListTools:-DotProduct(gL,convert(Row(R,Rw[j]),list)),j=1..nops(Rw))];
                nCi := [SearchAll(false,[seq(type(d[j],numeric),j=1..nops(d))])];
		nC  := {seq(Rw[nCi[j]],j=1..nops(nCi))};
		if ( nops(nC)>0 ) then
			num := [seq(ListTools:-DotProduct(convert(Row(R,nC[j]),list),gL),j=1..nops(nC))];
			den := [seq(num[j]+1,j=1..nops(num))];
			return Canc(num,den);
		else
			return [[],[]];
		end if;
	end proc; # rwExpressionJg

	rwExpressionL := proc(w::list,L::set,X::symbol,n::integer)::list; 
	description "computes the (non-cst terms of the) numerator and the denominator of r(l)/r(wl) restricted L";
		uses LinearAlgebra, ListTools;
		local R, aux, Rw, gL, nn, var, d, nCi, nC, den, num, j;
		R   := PoscoRoot(CartMatrix(X,n));
		aux := SetVec(R) intersect SetVec(MWeyl(-R,Reverse(w),X,n)); 
		if ( nops(aux)>0 ) then
			Rw := SinR(<seq(convert(aux[j],Vector[row]),j=1..nops(aux))>,R);
		else
			Rw := {};
		end if;
		gL  := Coord2WDD(GenPt(L,X,n),X,n);
		# nn  := [SearchAll(false,[seq(type(gL[j],numeric),j=1..nops(gL))])];
		# var := [seq(x[j],j=1..nops(nn))];
		# for j from 1 to nops(nn) do
		# 	gL[nn[j]] := var[j];
		# end do;
		d   := [seq(ListTools:-DotProduct(gL,convert(Row(R,Rw[j]),list)),j=1..nops(Rw))];
                nCi := [SearchAll(false,[seq(type(d[j],numeric),j=1..nops(d))])];
		nC  := {seq(Rw[nCi[j]],j=1..nops(nCi))};
		if ( nops(nC)>0 ) then
			num := [seq(ListTools:-DotProduct(convert(Row(R,nC[j]),list),gL),j=1..nops(nC))];
			den := [seq(num[j]+1,j=1..nops(num))];
			return Canc(num,den);
		else
			return [[],[]];
		end if;
	end proc; # rwExpressionL

	SameAssocOrb := proc(J::set,K::set,X::symbol,n::integer)
	description "returns true if J and K are in the same W' assoc orbit in D(X,n)";
		uses ListTools;
		local orbs, aux, wh, j, orb;
		orbs := AssocOrbs(X,n)[1];
		aux  := [seq( member(K,orbs[j]),j=1..nops(orbs) )];
		wh   := Search(true,aux);
		return member(J,orbs[wh]);
	end proc; # SameAssocOrb

	SameAssocOrbElem := proc(J::set,K::set,X::symbol,n::integer)
	description "returns a Weyl group element that maps J to K. Assumes SameAssocOrb(J,K) = true";
		uses ListTools;
		local orbs, aux, i, j, k, u;
		if ( SameAssocOrb(J,K,X,n)=false ) then
			return ERROR("These sets are not associated");
		else
			orbs := AssocOrbs(X,n);
			aux  := [seq(member(J,orbs[1][u]),u=1..nops(orbs[1]))];
			i    := Search(true,aux);
			j    := Search(J,orbs[1][i]);
			k    := Search(K,orbs[1][i]);
			return [op(orbs[2][i][k]),op(Reverse(orbs[2][i][j]))];
		end if;
	end proc; # SameAssocOrbElem

        SetVec := proc(Mv::Matrix)::set;
        description "Returns the Matrix as a set of vectors";
                local S, l, i;
                l := convert(Mv,list,nested);
                S := convert(l,set);
                return S;
        end proc; # SetVec

	SetWeyl := proc(S::set,w::list,X::symbol,n::integer)::set;
	description "S is a set with sign indicating the rows of the positive roots; a minus sign means a negative root";
		uses LinearAlgebra, ListTools;
		local R, aux, Po, P, Ne, N, Mp, Mn, M, j, k, v, s, ret;
		R   := PoscoRoot(CartMatrix(X,n));
		aux := [seq(evalb(S[j]>0),j=1..nops(S))];
		Po  := {SearchAll(true,aux)};
		P   := {seq(S[Po[j]],j=1..nops(Po))};
		Ne  := {SearchAll(false,aux)};
		N   := {seq(abs(S[Ne[j]]),j=1..nops(Ne))};
		Mp  := <seq(Row(R,P[j]),j=1..nops(P))>; 
		Mn  := <seq(Row(R,N[j])*(-1),j=1..nops(N))>;
		if ( RowDimension(Mp)>0 and RowDimension(Mn)>0 ) then
			M   := <Mp;Mn>;
		elif ( RowDimension(Mp)>0 ) then
			M := Mp;
		elif ( RowDimension(Mn)>0 ) then
			M := Mn;
		else
			M := convert([],Matrix);
		end if;
		ret := {};
		for j from 1 to RowDimension(M) do
			v := Weyl(Row(M,j),w,X,n);
			s := `+`(seq(v[k],k=1..Dimension(v)));	
			if ( s>0 ) then
				ret := ret union SinR(convert(v,Matrix),R);
			else
				aux := SinR(convert((-1)*v,Matrix),R);
				ret := ret union{-aux[1]};
			end if	 
		end do;
		return ret;
	end proc; # SetWeyl

        SimpRefl := proc(r::Vector,j::integer,X::symbol,n::integer)::Vector;
        description "Simple reflection on the i-th simple root on type (X,n)";
                uses LinearAlgebra, ArrayTools;
                local M, w, i;
                M := CartMatrix(X,n);
                if ( RowDimension(M)=0 ) then
                        return r;
                end if;
                w := convert(r,Array);
                w[j] := w[j] - foldl(`+`,0,seq(r[i]*M(i,j),i=1..NumElems(r)));
                return convert(w,Vector[row]);
        end proc; # SimpRefl

        SimpcoRoot := proc(X::symbol,n::integer)::Matrix;
        description "returns the usual simple roots as an n-by-m matrix, m depends on X";
                uses LinearAlgebra;
                local r, i, j;
                r := Matrix();
                if ( X<>A and X<>B and X<>C and X<>D and X<>E and X<>F and X<>G ) then
                        return r;
                end if;
                if ( n=1 ) then
                        return <1|-1>;
                end if;
                if ( n>1 ) then
                        if ( X=A ) then
                        for i from 1 to n do
                                for j from 1 to n+1 do
                                        if ( j=i ) then
                                                r(i,j) := 1;
                                        elif ( j=i+1 ) then
                                                r(i,j) := -1;
                                        else
                                                r(i,j) := 0;
                                        end if;
                                end do;
                        end do;
                        return r;
                end if;
                if ( X=B ) then
                        return DeleteColumn(SimpcoRoot(A,n),n+1);
                end if;
                if ( X=C ) then
                        return RowOperation(SimpcoRoot(B,n),n,2);
                end if;
                if ( X=D ) then
                        return RowOperation(SimpcoRoot(C,n),[n,n-1],1);
                end if;
                if ( X=E ) then
                        if ( n<6 ) or ( n>8 ) then
                                return r;
                        elif ( n=8 ) then
                                return << 1/2|-1/2|-1/2|-1/2|-1/2|-1/2|-1/2 |1/2>;
                                        <   1|   1|   0|   0|   0|   0|   0|   0>;
                                        <  -1|   1|   0|   0|   0|   0|   0|   0>;
                                        <   0|  -1|   1|   0|   0|   0|   0|   0>;
                                        <   0|   0|  -1|   1|   0|   0|   0|   0>;
                                        <   0|   0|   0|  -1|   1|   0|   0|   0>;
                                        <   0|   0|   0|   0|  -1|   1|   0|   0>;
                                        <   0|   0|   0|   0|   0|  -1|   1|   0>>
                        elif ( n=7 ) then
                                return DeleteRow(SimpcoRoot(E,8),8);
                        else
                                return DeleteRow(SimpcoRoot(E,7),7);
                        end if;
                end if;
                if ( X=F ) then
                        if ( n<>4 )  then
                                return r;
                        end if;
                        if ( n=4 ) then
                                return <<   0|   1|  -1|   0>;
                                        <   0|   0|   1|  -1>;
                        <   0|   0|   0|   1>;
                        < 1/2|-1/2|-1/2|-1/2>>;
                        end if;
                end if;
                if ( X=G ) then
                        if ( n<>2 ) then
                                return r;
                        end if;
                        if ( n=2 ) then
                                    return << 1|-1| 0>;
                                        <-2| 1| 1>>;
                                end if;
                        end if;
                end if;
        end proc; # SimpcoRoot

        SinR := proc(S::Matrix,R::Matrix)::set; 
        description "Each row is a vector. Returns a set indicating the position of S in R";
                uses LinearAlgebra;
                local r, s, l, i, p, j;
                r := RowDimension(R);
                s := RowDimension(S);
                if ( ColumnDimension(S)<>ColumnDimension(R) ) then
                        return {}; 
                end if;
                l :={};
                for i from 1 to s do;
                        p := 1;
                        j := 1;
                        while ( j<=r ) do;
                                if ( not evalb(convert(Row(R,j),list)=convert(Row(S,i),list)) ) then
                                        j := j+1;
                                        p := p+1;
                                        if ( j>r ) then
                                                return {};
                                        end if;
                                else
                                        j := r+1; 
                                        l := l union {p};
                                end if;
                        od;
                od;
                return l;
        end proc; # SinR
	
        SpecialcoRts := proc(c::Vector,X::symbol,n::integer)::set;
        description "Returns the special roots of a given quasi-residual subspace";
                uses LinearAlgebra;
                local S, R, m, d, i;
                S := {};
                R := PoscoRoot(CartMatrix(X,n));
                m := RowDimension(R);
                d := Array(1..m,[seq(DotProduct(c,Row(R,i).SimpcoRoot(X,n)),i=1..m)]);
                for i from 1 to m do
                        if ( abs(d[i])<0.00000001 ) then
                                d[i] := 0;
                        end if;
                od;
                for i from 1 to m do
                        if ( d[i]>=0 ) then
                                S := S union {i};
                        end if;
                od;
                return S;
        end proc; # SpecialcoRts
	
	StabJg := proc(J::set,g::list,X::symbol,n::integer)::list;
	description "computes the stabilizer of the space L = L(J,g)";
		uses ListTools, LinearAlgebra;
		local K, w, G, Kl, gK, Zax, Z, H, R, RiS, val, L, c, Gor, Gc, Hor, Hc, aux, bux, k, rtx, ret, j;
		K   := AssocOrbsWhich(J,X,n); # computes special representative subdiagrams
		w   := SameAssocOrbElem(J,K,X,n); # w s.t. w(J) = L
		G   := ParStab(K,X,n); # read the manually inputed Stab(K)
		Kl  := [seq(op(LWeyl({J[k]},w,X,n)),k=1..nops(J))]; # locks the ordering of K to get the right correspondence w(g)
		Zax := [SearchAll(0,g)];                 # the next 3 lines determine the reflection group generated by 
		Z   := {seq(Kl[Zax[k]],k=1..nops(Zax))}; # the zeroes of g.
		H   := ParWeyl(Z,X,n);                   #
		if ( nops(Zax)=0 ) then
			rtx := G;
		else
			R   := JPoscoRoot(convert(K,list),CartMatrix(X,n))(1,1);                                              # the next 6 lines determine the centre of
			RiS := JPoscoRoot(convert(K,list),CartMatrix(X,n))(1,2);                                              # the space (K=w(J),g)
			val := [seq(LinearAlgebra:-DotProduct(convert(R[k],Vector),convert(g,Vector)),k=1..RowDimension(R))]; #
			aux := {SearchAll(1,val)};                                                                            #
			L   := {seq(RiS[aux[j]],j=1..nops(aux))};                                                             #
			c   := Coord2WDD(CentL(L,X,n),X,n);                                                                   # 
			Gor := [seq(WDDWeyl(c,G[k],X,n),k=1..nops(G))];     # the next 3 lines determine which elements of G = Stab(K) fixes the centre of
			aux := [SearchAll(c,Gor)];                          # L = L(K,g)
			Gc  := [seq(redExp(G[aux[k]],X,n),k=1..nops(aux))]; #
			Hor := [seq(WDDWeyl(c,H[k],X,n),k=1..nops(H))];     ## the next 3 lines determine which elements of K = < reflections on zeroes of g>
			bux := [SearchAll(c,Hor)];                          ## fixes the centre of L = L(K,g)
			Hc  := [seq(redExp(H[bux[k]],X,n),k=1..nops(bux))]; ##
			rtx := ListProd(Gc,Hc); # rtx is the product Gc.Hc, which is thus the stabilizer of L=L(K,g)
		end if;
		ret := [seq([op(Reverse(w)),op(rtx[k]),op(w)],k=1..nops(rtx))]; # ret is the conjugated of rtx, so it is the stabilizer of L = L(K,g)
		return ret;
	end proc; # StabJg
	
	StabL := proc(L::set,X::symbol,n::integer)::list;
	description "computes the stabilizer of the space L";
		uses ListTools;
		local dat, w, J, g, G, j;
		dat := stdData(L,X,n);
		w   := dat[1];
		J   := dat[2];
		g   := dat[3];
		G   := StabJg(J,g,X,n);
		return [seq(redExp([op(Reverse(w)),op(G[j]),op(w)],X,n),j=1..nops(G))];
	end proc; # StabL
	
	stdData := proc(L::set,X::symbol,n::integer)::list;
	description "Given a pole space L, returns the standard data [w,J,g] of L";
		uses ListTools;
		local w, v, a, c, j, J, g; 
		w := stdLElem(L,X,n);
		v := WDDWeyl(Coord2WDD(GenPt(L,X,n),X,n),w,X,n);
		a := [seq(type(v[j],numeric),j=1..nops(v))];
		J := {SearchAll(true,a)};
		g := [seq(v[J[j]],j=1..nops(J))];
		return [w,J,g];
	end proc; # stdData

	stdLElem := proc(L::set,X::symbol,n::integer)::list;
	description "Given a pole space L, returns the Weyl group element that sends L to a standard parabolic one";
		local prim, m, r, s, k, j;
		if ( evalb(nops(L)=0) ) then # deals with the case L := {}.
			return [];
		end if;
		if ( L subset {seq(j,j=1..n)} ) then # deals with the case L already standard.
			return [];
		end if;
		if ( X=A or X=G ) then
                        m := n+1;
                elif ( X=E ) then
                        m := 8;
                else
                        m := n;
                end if;
		r := Coord2WDD(GenPt(L,X,n),X,n);
		s := subs({seq(y[k]=10^(2*k+2),k=1..m)},r); # corrected 17.05.21
		return WDDDomElem(s,X,n);
	end proc; # stdLElem
	
	stdLElemPar := proc(L::set,X::symbol,n::integer,J)::list;
	description "Given a pole space L, returns the Weyl group element in W(J) that sends L to a standard parabolic one";
		local m, r, s, k;
		if ( X=A or X=G ) then
                        m := n+1;
                elif ( X=E ) then
                        m := 8;
                else
                        m := n;
                end if;
		r := Coord2WDD(GenPt(L,X,n),X,n);
		s := subs({seq(y[k]=10^(2*k+2),k=1..m)},r); # corrected 17.05.21
		return WDDDomElemPar(s,X,n,J);
	end proc; # stdLElemPar
	
	stdWDD := proc(L::set,X::symbol,n::integer)::list;
	description "Assuming that L is in std position returns a WDD with variables such that sending x[j]=0 we get the cetre of L";
		uses ListTools;
		local c, g, t, i, x, j;
		c := Coord2WDD(CentL(L,X,n),X,n);
		g := Coord2WDD(GenPt(L,X,n),X,n);
		t := [SearchAll(false,[seq(type(g[j],numeric),j=1..nops(g))])];
		for i from 1 to nops(t) do
			g[t[i]] := x[i]+c[t[i]];
		end do;
		return g;
	end proc; # stdWDD

	subWeyl := proc(K::set,X::symbol,n::integer)::list;
	description "returns the std parabolic subgrou W(K) of W(X,n)";
		uses ListTools;
		local v, o, G, m, l, j, w, z;
		v    := [seq(1,j=1..n)];	
		o    := {v};
		G[0] := {[]};
		m    := 1;
		l    := 1;
		G[l] := {};
		while ( m>0 ) do
			for w from 1 to nops(G[l-1]) do
				for j from 1 to nops(K) do
					z := WDDWeyl(v,[op(K[j]),op(G[l-1][w])],X,n);
					if ( not member(z,o) ) then
						G[l] := G[l] union {[op(K[j]),op(G[l-1][w])]};
						o    := o union {z};
					end if;
				end do;	
			end do;
			m    := nops(G[l]);
			l    := l+1;
			G[l] := {};
		end do;
		G := `union`(seq(G[j],j=0..(l-1))[]);
		return G;
	end proc; # subWeyl
	
	tRelevnL := proc(L::set,X::symbol,n::integer)::set;
	description "computes the weyl group elements which are relevant (the (*) condition) on a given pole space L";
	#	uses ListTools, FileTools;
	#	local st, nam, s, W, test, ret, j, RET;
	#	W    := WeylPeel(X,n);
	#	for j from 1 to nops(W) do
	#		test := [seq(CanvRelevnL(L,W[j],X,n),j=1..nops(W))];
	#	ret  := [SearchAll(true,test)];
	#	RET  := {seq(W[ret[j]],j=1..nops(ret))};
	#	return RET;
	end proc; # tRelevnL

	TrvWDD := proc(v::list,Y::symbol,m::integer,K::list,X::symbol,n::integer)::Vector;
	description "Returns a list with all the points, parametrised as WDDs, which are crossed when sending t -> 0 in this crazy algorithm";
		local F, Ff, p, j, R, N, k;
		if ( not((m=5 and n=6) or (m=6 and n=7) or (m=7 and n=8)) ) then
                        return ERROR("We are only considering the sequence D5, E6, E7, E8.");
		end if;
		R  := PoscoRoot(CartMatrix(X,n));
		N  := LinearAlgebra:-RowDimension(R);
		F  := FFunc(v,Y,m,K,X,n);
		Ff := Ffactor(v,Y,m,K,X,n);
		p  := Vector(1..N);
		for j from 1 to nops(F[2]) do
			p[F[2][j]] := [seq(subs(t=solve(parse(cat(convert(Ff[2][j],string),"=0")),t),parse(convert(v[k],string))),k=1..n)];
		end do;
		for j from 1 to N do
			if ( not member(j,F[2]) ) then
				p[j] := sprintf("Select a value among %a",F[2])
			end if;
		end do;
		return p;
	end proc; # TrvWDD

        TypeE := proc(J::list)::list;
                    local Swap, P1, P2, P3, P4, P5, K, G0, G, i, PtA, PtD, PtE;
                ##### Start of Subprocedures #####
                Swap := proc(J::list)::list;
                uses ListTools;
                        local K, k, l;
                        K := J;
                        k := Search(1,J);
                        l := Search(2,J);
                        if ( k<>0 ) then
                                K[k] := 2;
                        fi;
                        if ( l<>0 ) then
                                K[l] := 1;
                        fi;
                        return convert(convert(K,set),list);
                end proc;    
                P1 := proc(J::list)::list;
                        local s, G, i;
                        PtA[1] := [[1]];
                        PtA[2] := [[1, 1]]; 
                        PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                        PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                        PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                        PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                        PtA[7] := Read("DataBase-TypeA/PtA7.mpl");
                        s := nops(JString(J));
                        G := foldl(ListProd,[],seq(PtA[JString(J)[i]],i=1..s));
                        return G;
                end proc;
                P2 := proc(J::list)::list;
                        local s, G, i;
                        PtA[1] := [[1]];
                        PtA[2] := [[1, 1]]; 
                        PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                        PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                        s := nops(JString(J[2..]));
                        G := ListProd(PtA[1],foldl(ListProd,[],seq(PtA[JString(J[2..])[i]],i=1..s)));
                end proc;
                P3 := proc(J::list)::list;
                        local K, s, G0, G, i;
                        PtA[1] := [[1]];
                        PtA[2] := [[1, 1]]; 
                        PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                        PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                        PtA[5] := Read("DataBase-TypeA/PtA5.mpl");
                        PtA[6] := Read("DataBase-TypeA/PtA6.mpl");
                        K := J;
                        if ( member(2,J) ) then
                                K[2] := 3;
                                s := nops(JString(K[2..]));
                                G0 := ListProd(PtA[1],foldl(ListProd,[],seq(PtA[JString(K[2..])[i]],i=1..s)));
                                G := [seq(G0[i][convert([[1,2]],permlist,nops(J))],i=1..nops(G0))];
                        else
                                K[1] := 3;
                                s := nops(JString(K));
                                G := foldl(ListProd,[],seq(PtA[JString(K)[i]],i=1..s));
                        fi;
                        return G;
                end proc;
                P4 := proc(J::list)::list;
                        local s, G, G0, i;
                        PtA[1] := [[1]];
                        PtA[2] := [[1, 1]]; 
                        PtA[3] := Read("DataBase-TypeA/PtA3.mpl");  
                        PtA[4] := Read("DataBase-TypeA/PtA4.mpl");
                        if ( member(2,J) ) then
                                s := nops(JString(J[5..]));
                                G0 := PtA[4];
                                G := ListProd([seq(G0[i][convert([[1,4,3,2]],permlist,4)],i=1..nops(G0))],foldl(ListProd,[],seq(PtA[JString(J[5..])[i]],i=1..s)));
                        else
                                s := nops(JString(J[4..]));
                                G0 := PtA[3];
                                G := ListProd([seq(G0[i][convert([[1,3,2]],permlist,3)],i=1..nops(G0))],foldl(ListProd,[],seq(PtA[JString(J[4..])[i]],i=1..s)));
                        fi;        
                        return G;
                end proc;
                P5 := proc(J::list)::list;
                        uses ListTools;
                        local K, s, G, G0, i;
                        PtA[1] := [[1]];
                        PtA[2] := [[1, 1]]; 
                        PtD[4] := Read("DataBase-TypeD/PtD4.mpl");
                        PtD[5] := Read("DataBase-TypeD/PtD5.mpl");
                        PtD[6] := Read("DataBase-TypeD/PtD6.mpl");
                        PtD[7] := Read("DataBase-TypeD/PtD7.mpl"); 
                        PtE[6] := Read("DataBase-TypeE/PtE6.mpl");
                        PtE[7] := Read("DataBase-TypeE/PtE7.mpl"); # needs to be computed
                        PtE[8] := Read("DataBase-TypeE/PtE8.mpl"); # needs to be computed
                        if ( not member(2,J) ) then
                                K := J;
                                K[1] := 2;
                                s := nops(JString(K));
                                G0 := [seq(Reverse(PtD[JString(K)[1]][i]),i=1..nops(PtD[JString(K)[1]]))];
                                G := ListProd(G0,foldl(ListProd,[],seq(PtA[JString(K)[i]],i=2..s)));
                        else
                                if ( not member(6,J) ) then
                                        s := nops(JString(J));
                                        G0 := [seq(PtD[5][i][convert([[1,4,3,2]],permlist,5)],i=1..nops(PtD[5]))];
                                        G := ListProd(G0,foldl(ListProd,[],seq(PtA[JString(J)[i]],i=2..s)));
                                else
                                        s := nops(JString(J));
                                        G:= ListProd(PtE[JString(J)[1]],foldl(ListProd,[],seq(PtA[JString(J)[i]],i=2..s)));
                                fi;
                        fi;
                        return G;
                end proc;
                ##### End of Subprocedures #####
                K := Swap(J);
                if ( not member(1,K) ) then
                        G0 := P1(K);
                else
                        if ( not member(4,K) ) then
                                G0 := P2(K);
                        else
                                if ( not member(3,K) ) then
                                        G0 := P3(K);
                                else
                                        if ( not member(5,K) ) then
                                                G0 := P4(K);
                                        else
                                                G0 := P5(K);
                                        fi;
                                fi;
                        fi;
                fi;
                if ( member(1,J) and member(2,J) ) then
                        G := [seq(G0[i][convert([[1,2]],permlist,nops(J))],i=1..nops(G0))];
                        return G;
                else    
                        return G0;
                fi;
        end proc; # TypeE
	
        vWeyl := proc(v::Vector,w::list,X::symbol, n::integer)::list;
        description "The action of a Weyl group element given in the rex w";
                uses LinearAlgebra;
                local B, s, j;
                B := SimpcoRoot(X,n); 
                s := proc(v,i::integer)::list; 
                        v - DotProduct(v,Row(B,i))*LieDual(Row(B,i));
                end proc;
                foldl(s,v,seq(w[-j],j=1..nops(w)));
        end proc; # vWeyl
		
        WDD2Coord := proc(g::list,X::symbol,n::integer)::Vector;
        description "Converts from to WDD to coordinates";
                uses LinearAlgebra;
                local m, v, Om, i;
                if ( X=A or X=G ) then
                        m := n+1;
                elif ( X=E ) then
                        m := 8;
                else
                        m := n;
                end if;
                Om := FundWeight(X,n);
                v := add(g[i]*Row(Om,i),i=1..n);
        end proc; # WDD2Coord        

        WDDDom := proc(g::list,X::symbol,n::integer)::list;
        description "Returns the dominant WDD in the orbit of g";
                local i, w;
                i := 1;
                w := g; 
                while ( i<=n ) do
                        if ( w[i]<0 ) then
                                w := WDDRefl(w,i,X,n);
                                i := 0;
                        end if;
                        i := i+1; 
                od; 
                return w;    
        end proc; # WDDDom

	WDDDomPar := proc(g::list,X::symbol,n::integer,J)::list;
        description "Returns W(J)-dominant WDD in the orbit of g";
                local i, w, m;
                i := 1;
                w := g; 
		m := nops(J);
                while ( i<=m ) do
                        if ( w[J[i]]<0 ) then
                                w := WDDRefl(w,J[i],X,n);
                                i := 0;
                        end if;
                        i := i+1; 
                od; 
                return w;    
        end proc; # WDDDomPar

	WDDDomElem := proc(g::list,X::symbol,n::integer)::list;
        description "Returns a (minimal length) weyl group element that sends g to the dominant element in the orbit";
                local i, v, w;
                i := 1;
                v := g; 
		w := [];
                while ( i<=n ) do
                        if ( v[i]<0 ) then
				w := [i,op(w)];
                                v := WDDRefl(v,i,X,n);
                                i := 0;
                        end if;
                        i := i+1; 
                od; 
                return w;    
        end proc; # WDDDomElem

	WDDDomElemPar := proc(g::list,X::symbol,n::integer,J)::list;
        description "Returns a (minimal length) weyl group element of W(J) that sends g to the dominant element in the orbit";
                local i, v, w, m;
                i := 1;
                v := g; 
		w := [];
		m := nops(J);
                while ( i<=m ) do
                        if ( v[J[i]]<0 ) then
				w := [J[i],op(w)];
                                v := WDDRefl(v,J[i],X,n);
                                i := 0;
                        end if;
                        i := i+1; 
                od; 
                return w;    
        end proc; # WDDDomElemPar

	WDDRootProd := proc(g::list,r::integer,X::symbol,n::integer) 
        description "Returns the value of the inner product of g and the root r"; 
                uses ListTools, LinearAlgebra; 
                local R, N, val; 
                R := PoscoRoot(CartMatrix(X,n)); 
                N := RowDimension(R); 
                if ( r < 1 or r > N) then 
                        return ERROR("Second entry is not a root"); 
		else
			val := ListTools:-DotProduct(g,convert(Row(R,r),list));
			return val;
                end if; 
        end proc; # WDDRootProd

        WDDRefl := proc(g::list,j::integer,X::symbol,n::integer)::list;
        description "Simple reflection on the j-th simple root on type (X,n) acting on WDDs";
                local w, i;
                w := convert(g,Array); 
                if ( LinearAlgebra[RowDimension](CartMatrix(X,n))=0 ) then
                        return g;
                end if;
                for i from 1 to nops(g) do
                        w[i] := g[i]-CartMatrix(X,n)[i][j]*g[j];
                od;
                return convert(w,list);
        end proc; # WDDRefl
        
        WDDWeyl := proc(g::list,w::list,X::symbol,n::integer)::list;
        description "The action of a Weyl group element given in the rex w";
                local s, j;
                s := proc(g,i::integer)::list; 
			WDDRefl(g,i,X,n);
                end proc;
                foldl(s,g,seq(w[-j],j=1..nops(w)));
        end proc; # WDDWeyl

        Weyl := proc(r::Vector,w::list,X::symbol,n::integer)::Vector;
        description "The action of a Weyl group element given in the rex w";
                uses ListTools;
                local s, j;
                s := proc(r,i::integer)::Vector; 
                        SimpRefl(r,i,X,n);
                end proc;
                foldl(s,r,seq(w[-j],j=1..nops(w)));
        end proc; # Weyl

	WeylD5E6 := proc(w::list)::list;
	description "embedds a Weyl group element of D5 into one of E6 wrt the choice of inclusion D5 in E6 used (reversed)";
		uses GroupTheory;
		local P;
		P := Perm([6,5,4,3,2,1]);
		return map2( PermApply,P,w );
	end proc; # WeylD5E6	

	WeylElms := proc(X::symbol,n::integer)::set;
	description "Returns the set of elements of the Weyl group";
		uses ListTools, FileTools;
		local st, W, v, o, G, m, l, j, w, z;
		st := cat("WeylGroups/W",X,n,".mpl");
		if ( Exists(st) ) then
			W := Read(st);
			return W;
		end if;
		v    := [seq(1,j=1..n)];	
		o    := {v};
		G[0] := {[]};
		m    := 1;
		l    := 1;
		G[l] := {};
		while ( m>0 ) do
			for w from 1 to nops(G[l-1]) do
				for j from 1 to n do
					z := WDDWeyl(v,[op(j),op(G[l-1][w])],X,n);
					if ( not member(z,o) ) then
						G[l] := G[l] union {[op(j),op(G[l-1][w])]};
						o    := o union {z};
					end if;
				end do;	
			end do;
			m    := nops(G[l]);
			l    := l+1;
			G[l] := {};
		end do;
		G := `union`(seq(G[j],j=0..(l-1))[]);
		return G;
	end proc; # WeylElms
	
	WeylElmsfrom2l := proc(orb::set,le::integer,X::symbol,n::integer)::set;
		uses ListTools;
		local i, v, o, aux, G, m, l, j, w, z;
		i := nops(orb[-1]);
		if ( le<=i ) then
			return ERROR("the end length is smaller or equal that the initial set of Weyl group elements.");
		end if;
		v    := [seq(1,j=1..n)];	
		o    := {seq(WDDWeyl(v,orb[j],X,n),j=1..nops(orb))};
		aux  := [SearchAll(true,[seq(evalb(nops(orb[j])=i),j=1..nops(orb))])];
		G[i] := {seq(orb[aux[j]],j=1..nops(aux))};
		m    := nops(G[i]);
		l    := i+1;
		G[l] := {};
		while ( m>0 and l<(le+1) ) do
			for w from 1 to nops(G[l-1]) do
				for j from 1 to n do
					z := WDDWeyl(v,[op(j),op(G[l-1][w])],X,n);
					if ( not member(z,o) ) then
						G[l] := G[l] union {[op(j),op(G[l-1][w])]};
						o    := o union {z};
					end if;
				end do;	
			end do;
			m    := nops(G[l]);
			l    := l+1;
			G[l] := {};
		end do;
		G := (`union`(seq(G[j],j=(i+1)..(l-1))[])) union orb;
		return G;
	end proc; # WeylElmsfrom2l	

	WeylElmsUpl := proc(le::integer,X::symbol,n::integer)::set;
	description "Returns the set of elements of the Weyl group";
		uses ListTools;
		local v, o, G, m, l, j, w, z;
		v    := [seq(1,j=1..n)];	
		o    := {v};
		G[0] := {[]};
		m    := 1;
		l    := 1;
		G[l] := {};
		while ( m>0 and l<(le+1)  ) do
			for w from 1 to nops(G[l-1]) do
				for j from 1 to n do
					z := WDDWeyl(v,[op(j),op(G[l-1][w])],X,n);
					if ( not member(z,o) ) then
						G[l] := G[l] union {[op(j),op(G[l-1][w])]};
						o    := o union {z};
					end if;
				end do;	
			end do;
			m    := nops(G[l]);
			l    := l+1;
			G[l] := {};
		end do;
		G := `union`(seq(G[j],j=0..(l-1))[]);
		return G;
	end proc; # WeylElmsUpl
	
	WeylLength := proc(w::list,X::symbol,n::integer)
	description "computes the length of the Weyl Group element w";
		uses ListTools;
		local R,l;
		R := PoscoRoot(CartMatrix(X,n));
		l := SetVec(R) intersect SetVec(MWeyl(-R,Reverse(w),X,n));
		return nops(l);
	end proc; # WeylLength

	WeylPeel := proc(X::symbol,n::integer)::list;
	description "peels the Weyl group by length";
		uses ListTools;
		local st, W, Le, j, N, We, l, lw, ret;
		st := cat("WeylGroups/W",X,n,".mpl");
		W  := Read(st);
		Le := [seq(nops(W[j]),j=1..nops(W))];
		N  := nops(W[-1]);
		We := Vector(N+1);
		for l from 1 to N+1 do
			lw := [SearchAll(l-1,Le)];
			We[l] := {seq(W[lw[j]],j=1..nops(lw))};
		end do;
		ret := [seq(We[j],j=1..(N+1))];
		return ret;
	end proc; # WeylPeel

	WeylRed := proc(w::list,X::symbol,n::integer)
	description "returns a reduced expression for w";
		uses ListTools;
		local g, j;
		g := WDDWeyl([seq(1,j=1..n)],w,X,n);
		return WDDDomElem(g,X,n);
	end proc; # WeylRed
	
	WeylReversel := proc(w::list,X::symbol,n::integer)
	description "returns a reduced expression for the element w0w, where w0 is the longest element";
		local wl;
		wl := longElem(X,n);
		return WeylRed([op(wl),op(w)],X,n);
	end proc; # WeylReversel

	WeylReverser := proc(w::list,X::symbol,n::integer)
	description "returns a reduced expression for the element ww0, where w0 is the longest element";
		local wl;
		wl := longElem(X,n);
		return WeylRed([op(w),op(wl)],X,n);
	end proc; # WeylReverser

	WeylStep := proc(wl::set,X::symbol,n::integer)::set;
	description "given a set wl of Weyl group elements, returns all the Weyl group elements of length +1 that can be obtained from wl";
		uses LinearAlgebra;
		local R, g, j, nw, orb, w, test, h, v;
		R   := PoscoRoot(CartMatrix(X,n));
		g   := [seq(1,j=1..n)];	
		nw  := {};
		orb := {};
		for w from 1 to nops(wl) do
			for j from 1 to n do
				test := SinR(convert(Weyl(Row(R,j),wl[w],X,n),Matrix),R); # tests is w(r[j])>0
				if ( nops(test)>0 ) then
					v := [op(wl[w]),j];
					h := WDDWeyl(g,v,X,n);
					if ( not member(h,orb) ) then
						orb := orb union {h};
						nw  := nw  union {v};
					end if;  
				end if;
			end do;	
		end do;
		return nw;
	end proc; # WeylStep

	WYmConj := proc(L::set,M::set,X::symbol,n::integer)::list;
	description "checks if two pole spaces are W(Y,m)-conjugate; returns a list [true,w'] if it is conjugate and w' sends L to M or [false,NULL]";
		uses ListTools;
		local p, rL, rM, aux, bux, wL, wM, JL, JM, gL, gM, w, a, v, wv, u, G, H, W, j, k, test, t;
		if ( X=E ) then
			if ( n=6 ) then
				p := [1,0,0,0,0,0];
			elif ( n=7 ) then
				p := [0,0,0,0,0,0,1];
			elif ( n=8 ) then
				p := [0,0,0,0,0,0,0,1];
			else
				return ERROR("Case not considered");
			end if
		else
			return ERROR("Case not considered");
		end if;
		if ( not evalb(nops(L)=nops(M)) ) then
			return [false,NULL];
		else
			if ( nops(L)=1 ) then
				rL := PoscoRoot(CartMatrix(X,n))[L[1]];
				rM := PoscoRoot(CartMatrix(X,n))[M[1]];
				if ( evalb( LinearAlgebra:-DotProduct(convert(p,Vector[row]),convert(rL,Vector[row]))=LinearAlgebra:-DotProduct(convert(p,Vector[row]),convert(rM,Vector[row])) ) ) then
					return [true,WYmHypConj(L,M,X,n)];
				else
					return [false,NULL];
				end if;
			else
				aux := stdData(L,X,n);
				bux := stdData(M,X,n);
				wL  := aux[1];
				JL  := aux[2];
				gL  := aux[3];
				wM  := bux[1];
				JM  := bux[2];
				gM  := bux[3];
				if ( not SameAssocOrb(JL,JM,X,n)  ) then
					return [false,NULL];
				else
					w := redExp(SameAssocOrbElem(JL,JM,X,n),X,n);
					v := [seq(a[j],j=1..n)];	
					for j from 1 to nops(JL) do
						v[JL[j]] := gL[j];
					end do;
					wv := WDDWeyl(v,w,X,n);
					if ( not evalb([seq(wv[JM[j]],j=1..nops(JM))]=gM)  ) then 
						return [false,NULL];
					else
						u    := [op(Reverse(wM)),op(w),op(wL)];
						G    := StabL(L,X,n);
						H    := StabL(M,X,n);
						W    := ListProd(H,ListProd([u],G));
						test := [seq(WDDWeyl(p,W[j],X,n),j=1..nops(W))];
						t    := Search(p,test);
						if ( t>0 ) then
							return [true,redExp(W[t],X,n)];
						else
							return [false,NULL];
						end if;
					end if;
				end if;
			end if;	
		end if;
	end proc; # WYmConj
	
	WD5E6Conj := proc(L::set,M::set)
	description "Returns true or false for the test is L is W' conj to M; only works if L is among the spaces computed in the Crazy Algorithm for E6";
		uses ListTools;
		local st, orb, sT, j;
		st  := cat("WmOrbits/E6/L",seq(cat(convert(L[j],string),","),j=1..nops(L)-1),convert(L[-1],string),".mpl");
		orb := Read(st);	
		sT  := Search(M,orb);
		if ( sT>0 ) then
			return true;
		else
			return false;
		end if;
	end proc; # WD5E6Conj

	WE6E7Conj := proc(L::set,M::set)
	description "Returns true or false for the test is L is W' conj to M; only works if L is among the spaces computed in the Crazy Algorithm for E6";
		uses ListTools;
		local st, orb, sT, j;
		st  := cat("WmOrbits/E7/L",seq(cat(convert(L[j],string),","),j=1..nops(L)-1),convert(L[-1],string),".mpl");
		orb := Read(st);	
		sT  := Search(M,orb);
		if ( sT>0 ) then
			return true;
		else
			return false;
		end if;
	end proc; # WE6E7Conj

	WYmConjCoarse := proc(L::set,M::set,X::symbol,n::integer)::list;
	description "checks if two pole spaces are W(Y,m)-conjugate; returns a list true if it is conjugate and w' sends L to M or false";
		uses ListTools;
		local p, rL, rM, aux, bux, wL, wM, JL, JM, gL, gM, w, a, v, wv, u, G, H, W, j, k, test, t;
		if ( X=E ) then
			if ( n=6 ) then
				p := [1,0,0,0,0,0];
			elif ( n=7 ) then
				p := [0,0,0,0,0,0,1];
			elif ( n=8 ) then
				p := [0,0,0,0,0,0,0,1];
			else
				return ERROR("Case not considered");
			end if
		else
			return ERROR("Case not considered");
		end if;
		if ( not evalb(nops(L)=nops(M)) ) then
			return false;
		else
			rL := PoscoRoot(CartMatrix(X,n))[L[1]];
			rM := PoscoRoot(CartMatrix(X,n))[M[1]];
			if ( evalb( LinearAlgebra:-DotProduct(convert(p,Vector[row]),convert(rL,Vector[row]))=LinearAlgebra:-DotProduct(convert(p,Vector[row]),convert(rM,Vector[row])) ) ) then
				return true;
			else
				return false;
			end if;
		end if;
	end proc; # WYmConjCoarse

	WYmHypConj := proc(L::set,M::set,X::symbol,n::integer)::list;
	description "Returns the W'-element that conjugates L onto M when L, M is a hyperplane";
		uses ListTools;
		local aL, aM, wL, wM, aux, j, w, u;
		aL := L;
		aM := M;
		wL := [];
		wM := [];
		while ( op(aL)>n ) do
			if ( n=6 ) then
				aux := [FindMinimalElement([seq(op(LWeyl(aL,[j],X,n)),j=2..6)],position)];
				wL  := [aux[2]+1,op(wL)];
			else
				aux := [FindMinimalElement([seq(op(LWeyl(aL,[j],X,n)),j=1..(n-1))],position)];
				wL  := [aux[2],op(wL)];
			end if;
			aL := {aux[1]};
		end do;
		while ( op(aM)>n ) do
			if ( n=6 ) then
				aux := [FindMinimalElement([seq(op(LWeyl(aM,[j],X,n)),j=2..6)],position)];
				wM  := [aux[2]+1,op(wM)];
			else
				aux := [FindMinimalElement([seq(op(LWeyl(aM,[j],X,n)),j=1..(n-1))],position)];
				wM  := [aux[2],op(wM)];
			end if;
			aM := {aux[1]};
		end do;
		w := SameAssocOrbElem(aL,aM,X,n);
		u := redExp([op(Reverse(wM)),op(w),op(wL)],X,n);
		return u;
	end proc; # WYmHypConj

	WYmOrb := proc(Ls::list,m::integer,n::integer)::list;
	description "Ls is a list of pole spaces. Returns a list with two entries; 1. set of representatives for each W(Y,m)-orbit, 2. the set of W(Y,m)-orbit";
		uses ListTools;
		local ORB, aux, bux, cux, N, j, orb;
		ORB := {};
		aux := Ls;
		N   := nops(Ls);
		while ( N>0 ) do;
			if ( n=6 ) then 
				bux := [seq(WD5E6Conj(aux[1],aux[j],E,n),j=1..N)];
			elif ( n=7 ) then
				bux := [seq(WE6E7Conj(aux[1],aux[j],E,n),j=1..N)];
			else
				bux := [seq(WYmConj(aux[1],aux[j],E,n),j=1..N)];
			end if;
			cux := [SearchAll(true,bux)];
			orb := [seq(aux[cux[j]],j=1..nops(cux))];
			ORB := ORB union {orb};
			aux := subsop(seq(cux[j]=NULL,j=1..nops(cux)),aux);
			N   := nops(aux);
		end do;
		return [[seq(ORB[j][1],j=1..nops(ORB))],ORB];
	end proc; # WYmOrb

	WYmOrbCoarse := proc(Ls::list,m::integer,n::integer)::list;
	description "Ls is a list of pole spaces. Returns a list with two entries; 1. set of representatives for each W(Y,m)-orbit, 2. the set of W(Y,m)-orbit";
		uses ListTools;
		local ORB, aux, bux, cux, N, j, orb;
		ORB := {};
		aux := Ls;
		N   := nops(Ls);
		while ( N>0 ) do;
			bux := [seq(WYmConjCoarse(aux[1],aux[j],E,n),j=1..N)];
			cux := [SearchAll(true,bux)];
			orb := [seq(aux[cux[j]],j=1..nops(cux))];
			ORB := ORB union {orb};
			aux := subsop(seq(cux[j]=NULL,j=1..nops(cux)),aux);
			N   := nops(aux);
		end do;
		return [{seq(ORB[j][1],j=1..nops(ORB))},ORB];
	end proc; # WYmOrbCoarse

	WYmSort := proc(Mt::Matrix,m::integer,n::integer)::list;
	description "Mt is a matrix whose second colum is pole spaces and the first row is a header. Returns a list of ordered submatrices of orbits";
		uses ListTools, LinearAlgebra;
		local Ls, ORB, aux, bux, cux, N, j, k, orb;
		ORB := {};
		Ls  := [seq(Mt(j,2),j=2..RowDimension(Mt))];
		aux := [seq(j,j=1..nops(Ls))];
		N   := nops(Ls);
		while ( N>0 ) do;
			if ( n=6 ) then 
				bux := [seq(WD5E6Conj(Ls[aux[1]],Ls[aux[j]],E,n),j=1..N)];
			else
				bux := [seq(WYmConj(Ls[aux[1]],Ls[aux[j]],E,n),j=1..N)];
			end if;
			cux := [SearchAll(true,bux)];
			orb := [seq(aux[cux[j]],j=1..nops(cux))];
			ORB := ORB union {orb};
			aux := subsop(seq(cux[j]=NULL,j=1..nops(cux)),aux);
			N   := nops(aux);
		end do;
		return [seq(Mt([1,seq(ORB[j][k]+1,k=1..nops(ORB[j]))],..),j=1..nops(ORB))];
	end proc; # WYmSort
	
        YminXn := proc(Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
        description "Returns a list indicating how (Y,m) sits inside (X,n). Returned list is s.t. li[i]='row of Rb that corresponds to the i-th row of Rs'";
                uses LinearAlgebra, ListTools;
                local Rb, Rs, R, i, li, j; 
				Rb := PoscoRoot(CartMatrix(X,n));
				Rs := PoscoRoot(CartMatrix(Y,m));
				R  := Matrix(RowDimension(Rs),n);
				for i from 1 to RowDimension(Rs) do
					for j from 1 to m do
						R(i,K[j]) := Rs(i,j);
					end do;
				end do;
				li := [];
				for i from 1 to RowDimension(R) do
					for j from 1 to RowDimension(Rb) do
						if ( evalb(convert(Row(R,i),list)=convert(Row(Rb,j),list)) ) then
							li := [op(li),j];
						end if;
					end do;        
				end do;
				return li;
        end proc; # YminXn

        YminXnCp := proc(Y::symbol,m::integer,K::list,X::symbol,n::integer)::list;
        description "Returns a list indicating the complement of (Y,m) in (X,n).";
                uses LinearAlgebra;
                local N, li, i; 
				N  := RowDimension(PoscoRoot(CartMatrix(X,n)));
				li := {seq(i,i=1..N)} minus convert(YminXn(Y,m,K,X,n),set);
                return convert(li,list);
        end proc; # YminXnCp 

        ZeroSet := proc(g::list,R::Matrix)::set; 
        description "Returns a set indexing the pos roots that are zero on g";
                uses LinearAlgebra;
                local d, i, z;
                d := Vector(RowDimension(R));
                for i from 1 to numelems(d) do
                        d[i] := DotProduct(convert(g,Vector),R[i]);
                od;
                z := {};
                for i from 1 to numelems(d) do
                        if ( d[i]=0 ) then
                                z := z union {i};
                        end if;
                od;
                return z;
        end proc; # ZeroSet

        ZeroSetL := proc(L::set,X::symbol,n::integer)::set; 
        description "Returns a set indexing the pos roots that are constantly zero on L";
                uses LinearAlgebra, ListTools;
                local R, csL, cL, dL, zL, i;
                R   := PoscoRoot(CartMatrix(X,n)).SimpcoRoot(X,n);
                csL := Cst(L,X,n);
                cL  := CentL(L,X,n);
                dL  := [seq(DotProduct(Row(R,csL[i]),cL),i=1..nops(csL))];
                zL  := [SearchAll(0,dL)];
                return convert(zL,set);
        end proc; # ZeroSetL
        
end module; # QResidual
with(QResidual):
with(LinearAlgebra):
with(ListTools):
interface(rtablesize=infinity):        
