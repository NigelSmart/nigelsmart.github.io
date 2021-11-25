
#
# Code Copyright Florian Hess, 8th June 2000
#

KashVersionIsWD := false;  #switch to true for faster point mapping

##########################################################################

AlffInfo := function(arg)
   return true;
end;

#AlffInfo := Print;  #switch on for intermediate print out

AlffDivisorGcd := function(D1, D2)
   local l1, l2, x, j, D;
   l1 := AlffDivisorPlaces(D1);
   l2 := AlffDivisorPlaces(D2);
   D := AlffDivisor(AlffDivisorAlff(D1));
   for x in l1 do
      j := PositionProperty(l2, a->a[1] = x[1]);
      if not j = false then
         D := D + Minimum(x[2], l2[j][2])*x[1];
      fi;
   od;
   return D;
end;
 

AlffDivisorValuation := function(P, D)
   local l, i;
   if not AlffPlaceAlff(P) = AlffDivisorAlff(D) then
      return Error("different function fields");
   fi;
   l := AlffDivisorPlaces(D);
   i := Position(List(l, x->x[1]), P);
   if i = false then
      return 0;
   else
      return l[i][2];
   fi;
end;


AlffHyperellipticReduce := function(arg)
#
#  Performs some coefficient reduction for hyperelliptic alffs
#  over finite fields. Maps also divisors over.
#  The method may unfortunately not work well for large examples ...
#
   local F, infty, r, P, f, G, LG, D, T, a, L, min, Y, Px, DG, DD, 
         PlaceOfDegOne, LessEqual;
   LessEqual := function(a1, a2)
      local v1, v2, pos, i;
      if IsFFElt(a1) then
         if Characteristic(FFEltFF(a1)) > 2 then
            return Error("Cannot compare in char > 2");
         fi;
         v1 := FFEltToList(a1, FF(2));
         v2 := FFEltToList(a2, FF(2));
         pos := Position(v1+v2, FFGenerator(FF(2)));
         if pos = false then
            return true;
         else
            return _IsZero(v1[pos]);
         fi;
      elif IsPoly(a1) then
         if PolyDeg(a1) < PolyDeg(a2) then
            return true;
         elif PolyDeg(a1) > PolyDeg(a2) then
            return false;
         fi;
         v1 := PolyToList(a1);
         v2 := PolyToList(a2);
         for i in [1..Length(v1)] do
            if not v1[i] = v2[i] then
               return LessEqual(v1[i], v2[i]);
            fi;   
         od;
         return true;
      elif IsQfe(a1) then
         if not Den(a1) = Den(a2) then
            return LessEqual(Den(a1), Den(a2));
         else
            return LessEqual(Num(a1), Num(a2)); 
         fi;   
      elif IsAlffElt(a1) then
         v1 := AlffEltToList(a1);
         v1 := v1[1] / v1[2];
         v2 := AlffEltToList(a2);
         v2 := v2[1] / v2[2];
         for i in [1..Length(v1)] do
            if not v1[i] = v2[i] then
               return LessEqual(v1[i], v2[i]);
            fi;   
         od;
         return true;
      elif IsAlffPlace(a1) then
         if a1 = a2 then
            return true;
         elif not AlffPlaceIsFinite(a1) = AlffPlaceIsFinite(a2) then
            return AlffPlaceIsFinite(a1);
         fi;
         v1 := AlffIdealBasis(AlffPlaceIdeal(a1));
         v2 := AlffIdealBasis(AlffPlaceIdeal(a2));
         for i in [1..Length(v1)] do
            if not v1[i] = v2[i] then
               return LessEqual(v1[i], v2[i]);
            fi;   
         od;
         return true;
      else
         return Error("unsupported type in LessEqual()");
      fi;
   end;
   PlaceOfDegOne := function(F)
      local k, w, l, pos, x, q, i;
      k := AlffConstField(F);
      x := AlffVarT(F);
      l := AlffPlaceSplit(F, x);
      pos := PositionProperty(l, p->AlffPlaceDeg(p)=1);
      if not pos = false then
         return l[pos];
      fi;
      q := AlffConstFieldSize(F);
      w := FFPrimitiveElt(k);
      for i in [1..q-1] do
         l := AlffPlaceSplit(F, x + w^i);
         pos := PositionProperty(l, p->AlffPlaceDeg(p)=1);
         if not pos = false then
            return l[pos];
         fi;
      od;
      l := AlffPlaceSplit(F, 1/x);
      pos := PositionProperty(l, p->AlffPlaceDeg(p)=1);
      if not pos = false then
         return l[pos];
      fi;
      return false;
   end;
   F := arg[1];
   L := Flat(arg{[2..Length(arg)]});
   if not AlffPlaceSplitType(F, 1/AlffVarT(F)) = [ [2,1] ] then
      D := List(AlffDivisorPlaces(AlffDifferent(F)), x->x[1]);
      # there is always a ramified place of degree one, hopefully ...
      D := Filtered(D, p->AlffPlaceDeg(p)=1);
      if Length(D) > 0 then
         Sort(D, LessEqual);
         P := D[1];
        #P := RandomList(D);
      else
         if Length(AlffPlaceSplitType(F, 1/AlffVarT(F))) = 2 then
            P := false;
         else
            P := PlaceOfDegOne(F);         #fails if there are none
            #P := AlffPlaceRandom(F, 1);  
            if P = false then
               return Error("Could not find a place of degree one");
            fi;
         fi;
      fi;
      if not P = false then  # push the rational point P to infty 
         min := AlffVarT(F) - Eval(AlffPlaceMin(P), 0);
         f := AlffOrderPoly(AlffOrderEqFinite(F));
         f := List(PolyToList(f), x->Eval(x + 0*AlffVarT(F), min));
         f := List(f, x->Eval(x + 0*AlffVarT(F), 1/AlffVarT(F)));
         f := f * Iterated(List(f, x->Den(x + 0*AlffVarT(F))), Lcm);
         f := Poly(PolyAlg(AlffVarY(F)), f);
         G := Alff(f);
         Y := AlffEltGenY(G);
         LG := [];
         for D in L do
            DD := List(AlffDivisorIdeals(D), x->AlffIdealBasis(x^-1));
            DD := List(DD, x->List(x, y->AlffEltMove(y, 
                          AlffOrderEqFinite(F))));
            DD := List(DD, x->List(x, y->AlffEltToList(y)));
            DD := List(DD, x->List(x, y->List(y[1], z->Eval(Eval(z, min) + 
                          0*AlffVarT(F), 1/AlffVarT(F))) /
                          Eval(Eval(y[2], min) + 0*AlffVarT(F), 
                               1/AlffVarT(F)) ));
            DD := List(DD, x->List(x, y->Sum([1..Length(y)], 
                          i->y[i]*Y^(i-1))));
            DG := AlffDivisor(Sum(DD[1], x->AlffEltMove(x, 
                           AlffOrderMaxFinite(G))*AlffOrderMaxFinite(G)),
                           Sum(DD[1], x->AlffEltMove(x, 
                               AlffOrderMaxInfty(G))*AlffOrderMaxInfty(G)));
            Px := AlffPlaceSplit(G, AlffVarT(G));
            for P in Px do
               DG := DG - AlffDivisorValuation(P, DG)*P + 
                     Minimum(List(DD[2], y->AlffEltValuation(P, y)))*P;  
            od;
            Add(LG, DG);
            if not AlffDivisorDeg(D) = AlffDivisorDeg(DG) then
               return Error("something wrong I");
            fi;
         od;
         if Length(LG) > 0 then
            F := G;
            L := LG;
         else
            F := G;
         fi;   
      fi;
   fi;
   
   # reduction using a rational point at infty
   infty := Filtered(AlffPlaceSplit(F, 1/AlffVarT(F)), x->AlffPlaceDeg(x)=1);
   Sort(infty, LessEqual);
   infty := infty[1];
   #infty := RandomList(infty);
   r := 1;
   while PolyDeg(AlffEltMinPoly(
           Reversed(AlffDivisorLBasis(r*infty))[1])) < 2 do
      r := r + 1;
   od;
   a := AlffEltMove(Reversed(AlffDivisorLBasis(r*infty))[1], 
                AlffOrderEqFinite(F));
   T := List([1..AlffDeg(F)], i->AlffEltToList(a^(i-1)));
   T := List(T, a->a[1]/a[2]);
   IsMatCheck(T);
   T := T^-1;
   G := Alff(AlffEltMinPoly(a));
   LG := [];
   for D in L do
      DG := List(AlffDivisorIdeals(D), x->AlffIdealBasis(x^-1));
      DG := List(DG, x->List(x, y->AlffEltMove(y, AlffOrderEqFinite(F))));
      DG := List(DG, x->List(x, y->AlffEltToList(y)));
      DG := List(DG, x->List(x, y->y[1]/y[2]));
      DG := List(DG, x->List(x, y->ListApplyMatAdd(y, T)));
      DG := List(DG, x->List(x, y->AlffElt(AlffOrderEqFinite(G), y)));
      DG[1] := List(DG[1], y->AlffEltMove(y, AlffOrderMaxFinite(G)));
      DG[2] := List(DG[2], y->AlffEltMove(y, AlffOrderMaxInfty(G)));
      DG := List(DG, x->Sum(x, y->y*AlffEltOrder(y)));
      DG := AlffDivisor(DG[1], DG[2]);
      AlffDivisorPlaces(DG);
      Add(LG, DG);
      if not AlffDivisorDeg(D) = AlffDivisorDeg(DG) then
         return Error("something wrong II");
      fi;
   od;
   
   GASMAN("g");
   
   if Length(LG) = 0 then
      return G;
   else
      return Flat([G, LG]);
   fi;
end;



AlffWeilRestriction := function(arg)
#
#  Given an elliptic function field E: y^2 + xy + x^3 + ax^2 + b
#  n and and optionally some places of degree one, return the 
#  hyperelliptic curve in the Weil restriction and the image of 
#  the given places.
#
#  Calling is AlffWeilRestriction(E, n [, p1, p2, p3, ... , reduce] ).
#
#  Returns F or [ F, D1, D2, D3, ... ] such that e.g. if (p2-p3) = m*(p1-p3) 
#  then (D1-D3) = m*(D2-D3).  The pi may not be over x=0 or x=infty, which
#  makes a translation of the origin necessary.
#
#  reduce is true or false. If it is false no reduction is done at the
#  end and results (especially point mapping) are obtained faster but also
#  "uglier".
#   
#  Program contains some special assumptions making the trafos easier, 
#  they may fail. Should be no problem in general.
#
   local E, P, K, k, p, q, n, m, a, b, e, y, beta, delta, deltabef,
         alpha, gamma, gammabef,
         z, zold, Kc, kc, kcy, c, cold, i, j, M, X, Y, YY, s, 
         ss, t, cc, mu, lam0, lamss, sigma,
         ct, Yfix, xp, yp, pl, f, cfix, zincfix, F, D, zp, yp, cp,
         P1, xp, Fs, Ys, P1, pp, DL, cfixtmp, fp, kp, tr, v, l, M, ff2,
         ff2sig, sig, f_mipo, f_ev, h, v, vv, Sig, Sig1, tmp, eps, pg,
         reduce;  
   
   # some setups
   
   E := arg[1];
   n := arg[2];
   P := Filtered(arg, x->IsAlffPlace(x));
   K := AlffConstField(E);
   
   if not false in arg then
      reduce := true;
   else
      reduce := false;
   fi;
   
   if not FFSize(K)[2] mod n = 0 then
      return Error("n does not divide the field degree over GF(2)");
   fi;
   
   k := FF(2, FFSize(K)[2] / n);
   p := 2;
   q := p^(FFSize(K)[2] / n);
   FFEmbed(k, K);
   a := PolyToList(Eval(AlffPoly(E), 0))[2];
   e := PolyToList(Eval(AlffPoly(E), 0))[3];
   b := PolyToList(Eval(AlffPoly(E), 0))[4];
   alpha := List([0..n-1], i->a^(q^i));
   beta := List([0..n-1], i->b^(q^i));
   eps :=  List([0..n-1], i->e^(q^i));
   delta := List([1..n-1], i->(beta[1] + beta[i+1])^(q^n/p) + 
                               (eps[1] + eps[i+1])^(q^n));
   gamma := List([1..n-1], i->alpha[1] + alpha[i+1]);
   deltabef := Copy(delta);
   gammabef := Copy(gamma);
   c := AlffVarT(E);
   cold := AlffVarT(E);
   Kc := PolyAlg(c);
   kc := PolyAlg(k);
   y := AlffVarY(E);
   
   if not AlffPoly(E) = y^2 + c*y + c^3 + a*c^2 + e*c + b then
      return Error("equation does not have the required shape");
   fi;
   
   if not ForAll(P, AlffPlaceIsFinite) then
      return Error("cannot map infinite place");
   fi;
   
   GASMAN("g");GASMAN("C");
   
   # Mipo on b
   ff2 := FF(2);
   ff2sig := PolyAlg(ff2, "sig");
   sig := Poly(ff2sig, [1,0]);
   l := [ e^2 + b ];
   i := 0;
   repeat
      i := i + 1;
      Add(l, (e^2 + b)^(q^i));
      M := List(l, x->FFEltToList(x, ff2));
      IsMatCheck(M);
      M := MatKernel(M);
   until MatRows(M) > 0;
   f_mipo := Poly(ff2sig, Reversed(M[1]));
   if not _IsZero(Eval(f_mipo, 1)) then
      f_ev := f_mipo * (sig + 1);
   else
      f_ev := f_mipo;
   fi;
   h := (sig^n + 1) / f_ev;
   m := PolyDeg(f_ev);
   
   AlffInfo("f_mipo is ", f_mipo, "\n");
   AlffInfo("f_ev is   ", f_ev, "\n");
   AlffInfo("h is      ", h, "\n");
   
   GASMAN("g");GASMAN("C");
   
   # v := f_ev(sig)s_0
   l := Reversed(PolyToList(f_ev));
   v := 0 + 0*FFGenerator(K);
   for i in [1..PolyDeg(f_ev)+1] do
      if not _IsZero(l[i]) then
         v := v + a^(q^(i-1));
      fi;
   od;
   v := Factor(AlffVarT(E)^2 + AlffVarT(E) + v);
   if not Length(v) = 2 then
      return Error("something is wrong 0,1");
   fi;
   v := Eval(v[1][1], 0);
   
   AlffInfo("v is      ", v, "\n");
   
   # vv := h(sig)v
   l := Reversed(PolyToList(h));
   vv := 0 + 0*FFGenerator(K);
   for i in [1..PolyDeg(h)+1] do
      if not _IsZero(l[i]) then
         vv := vv + v^(q^(i-1));
      fi;
   od;
   
   AlffInfo("vv is     ", vv, "\n");
   
   if not _IsZero(vv) then
      if _IsZero(Eval(h, 1)) then
         return false;
      fi;   
      AlffInfo("v -> v + 1\n");
      v := v + 1;
   fi;
   
   GASMAN("g");GASMAN("C");
   
   # Frobenius operation on k-space of dim m+n
   Sig := List(MatToRowList(MatId(k, m)){[2..m]}, 
               x -> Concatenation(x, 0*[1..n]));
   Add(Sig, Concatenation( Reversed(PolyToList(PolyMove(f_ev, k)){[2..m+1]}), 
           FFEltToList(v, k)));
   Append(Sig, List([1..n], i->Concatenation(0*[1..m], 
           FFEltToList(FFGenerator(K, k)^((i-1)*q), k))));   
   IsMatCheck(Sig);
   
   if not Sig^n = MatId(k, m+n) then
      return Error("something is wrong 0,III");
   fi;
   
   # lemma 3
   # we will have M (s_0 + s_1, ..., s_0 + s_(n-1))^t = (t_1, ..., t_(n-1))^t
   # we have delta[i] = 0 iff i > m-1.
   # reminder: c equals t_(m-1) at the end
   
   AlffInfo("delta before is ", delta, "\n");
   
   m := 1;
   M := MatId(K, n-1); 

   for i in [1..n-1] do
      for j in [1..i-1] do
         if not _IsZero(delta[j]) then
            M[i] := M[i] + (delta[i]/delta[j])^(q^n/p) * M[j];
            gamma[i] := delta[i]/delta[j]*gamma[j] + gamma[i];
            delta[i] := delta[i]/delta[j] + (delta[i]/delta[j])^(q^n/p);
         fi;   
      od;
      
      if not _IsZero(delta[i]) then
         m := m + 1;
      fi;
   od;
   
   IsMatCheck(M);
   z := c;
   for i in [1..n-1] do
      if not _IsZero(delta[i]) then
         z := Eval(z, ((c^2 + c) - gamma[i]) / delta[i]);
      fi;   
   od;
   zold := z;
   
   if not m = PolyDeg(f_ev) then
      return Error("something is wrong 0,II");
   fi;
   
   AlffInfo("delta after is ", delta, "\n");
   AlffInfo("m is ", m, "\n");
   AlffInfo("z is ", z, "\n");
   
   GASMAN("g");GASMAN("C");
   
   # create F:  x = 1/z. z = z(c). This relation is non rational
   F := Alff( z^3*y^2 + z^2*y + 1 + a*z + e*z^2 + b*z^3 );
   
   # find original X, Y etc.
   c := AlffEltGenT(F);
   z := Eval(z, c);
   X := 1/z;
   Y := AlffEltGenY(F);
   if not _IsZero(Y^2 + X*Y + X^3 + a*X^2 + e*X + b) then
      return Error("something is wrong I");
   fi;
   vv := [];
   for i in [1..n] do
      Sig1 := Sig^(i-1);
      Sig1 := Sig1[1];
      Sig1 := Sig1{[m+1..n+m]};
      Add(vv, Sig1);
   od;
   vv := List(vv{[2..n]}, x->Sum([1..n], 
                 i->FFEltMove(x[i], K)*FFGenerator(K, k)^(i-1)));
   vv := MatTrans(K, [vv]);
   t := MatToColList(M*vv)[1];
   for i in [m..n-1] do
      if not _IsZero(Eval(AlffVarT(E)^2 + AlffVarT(E) + gamma[i], t[i])) 
         then
         return Error("something is wrong 0,IV");
      fi;
   od;
   if m > 1 then
      t[m-1] := c;
      for i in Reversed([1..m-2]) do
         t[i] := (t[i+1]^2 + t[i+1] - gamma[i+1])/delta[i+1]; 
      od;
   fi;
   ss := ListApplyMatAdd(t, MatTrans(M)^-1);
   AlffInfo("t is ", t, "\n");
   AlffInfo("ss is ", ss, "\n");
   if not ForAll(List([1..n-1], i->ss[i]^2 + ss[i] + gammabef[i] + 
              deltabef[i]*z), _IsZero) then
      return Error("something is wrong II");
   fi;
   s := [];
   s[1] := (Y + beta[1]^(q^n/p)) / X;
   for i in [2..n] do
      s[i] := ss[i-1] + s[1];
   od;
   YY := List([1..n], i->X*s[i] + beta[i]^(q^n/p));
   if not ForAll(List([1..n], i->YY[i]^2 + X*YY[i] + X^3 + a^(q^(i-1))*X^2 
              + e^(q^(i-1))*X + b^(q^(i-1))), _IsZero) then
      return Error("something is wrong III");
   fi;
   
   # get the frobenius conjugates of c
   sigma := Product([2..n], i->(1,i));
   cc := [];
   if m > 1 then
      for i in [1..n] do
         for j in [2..n] do
            ss[j-1] := s[1^(sigma^(i-1))] + s[j^(sigma^(i-1))];
         od;
         v := List(MatToColList(MatTrans(M))[m-1], u->u^(q^(i-1)));
         cc[i] := ListApplyListAdd(ss, v);
      od;
   else
      cc := List([1..n], i-> c);
   fi;
   if not ForAll(List([1..n], i->Eval(Poly(Kc, List(PolyToList(zold), 
              u->u^(q^(i-1)))), cc[i])) - zold, _IsZero) then
      return Error("something is wrong IV");
   fi;
   
   AlffInfo("YY is ", YY, "\n"); 
   AlffInfo("cc is ", cc, "\n"); 
   
   GASMAN("g");GASMAN("C");
   
   # trace Y and c
   # get fixed variable of c
   
   if n mod 2 = 0 then
      mu := FFGenerator(K);
      while _IsZero(Trace(mu, k)) do
         mu := mu*FFGenerator(K);
      od;
      mu := mu / FFEltMove(Trace(mu, k), K); 
   else
      mu := 1 + 0*FFGenerator(K);
   fi;
   
   lam0 := Eval(PolyDeriv(zold), 0);
   Yfix := Sum([1..n], i->mu^(q^(i-1))*YY[i]);   
   cfix := Sum([1..n], i->(mu*lam0)^(q^(i-1))*cc[i]);
   
   lamss := cfix - lam0*cc[1];
   lamss := AlffEltToList(lamss);
   if not _IsOne(lamss[2]) or PolyDeg(lamss[1][1]) > 0 or 
      not ForAll(lamss[1]{[2..Length(lamss[1])]}, _IsZero) then
      return Error("lamss is not a constant!");
   fi;
   lamss := Eval(lamss[1][1], 0);
   
   zincfix := PolyMove(Eval(zold, (cold - lamss) / lam0), kc);
   
   AlffInfo("Yfix is ", Yfix, "\n"); 
   AlffInfo("cfix is ", cfix, "\n"); 
   AlffInfo("z in cfix is ", zincfix, "\n");
   
   GASMAN("g");GASMAN("C");
   
   if n mod 2 = 0 then
      if false then
         # don't know the equation (eps, e is missing)
         tr := Sum([1..n], i->mu^(q^(i-1)));
         if not _IsZero( Yfix^2 + tr*X*Yfix + tr^2*( X^3 + a*X^2 ) + 
                    Sum([1..n], i->(mu^2*b)^(q^(i-1))) ) then
            return Error("something is wrong VI");
         fi;
         if not _IsZero( Yfix^2 + FFEltMove(Trace(mu, k), K)*X*Yfix 
                    + FFEltMove(Trace(mu, k), K)^2*( X^3 + a*X^2 ) + 
                    FFEltMove( Trace(mu^2*b, k), K) ) then
            return Error("something is wrong VI");
         fi;
      fi;   
   else
      if not _IsZero( Yfix^2 + X*Yfix + X^3 + FFEltMove(Trace(a, k), K)*X^2 + 
               FFEltMove(Trace(e, k), K)*X + FFEltMove(Trace(b, k), K) ) then
         return Error("something is wrong VI");
      fi;
   fi;
   
   # get rational equation in Yfix and cfix 
   f := PolyToList(AlffEltMinPoly(Yfix));
   if Length(f) < 3 then
      return Error("element does not generate full fixed field!!!\n");
   fi;
   f := List(f, p->Eval(p, (cold - lamss) / lam0));
   f := f / PolyToList(f[1])[1];
   if not _IsZero(Sum([0..2], i->
              Eval(Reversed(f)[i+1] + 0*AlffVarT(F), cfix)*Yfix^i)) then
      return Error("something is wrong VI,2");
   fi;

   f := List(f, p->PolyMove(p + 0*cold, kc));
   kcy := PolyAlg(kc);
   f := Poly(kcy, f);
   
   Fs := Alff(f);
   Ys := AlffEltGenY(Fs);
   
   GASMAN("g");GASMAN("C");
   
   # now map the places
   DL := [];
   for pl in P do
      
      AlffInfo("map place to F\n");
      
      # first to F
      yp := AlffEltEval(pl, AlffEltGenY(E));
      xp := AlffEltEval(pl, AlffEltGenT(E));
      if xp = false or _IsZero(xp) then
         return Error("cannot map zeros/poles of x");
      fi;
      if xp = false then
         # too lazy to think about ...
         P1 := AlffDivisorGcd(
                       AlffDivisorNum(AlffDivisor(1/Y)),
                       AlffDivisorNum(AlffDivisor(1/X)));
      else
         P1 := AlffDivisorGcd(
                       AlffDivisorNum(AlffDivisor(Y + yp)),
                       AlffDivisorNum(AlffDivisor(X + xp)));
      fi;
      if not AlffDivisorDeg(P1) = 2^(m-1) then
         return Error("divisor deg not 2^(m-1)!!!");
      fi;
      P1 := AlffDivisorSupp(P1); # no ramification happens at finite places
      
      AlffInfo("length of P1 is ", Length(P1), "\n");
      
      D := AlffDivisor(Fs);
      for p in P1 do
         
         AlffInfo("map place to F'\n");
         
         yp := AlffEltEval(p, Yfix);
         cp := AlffEltEval(p, cfix);
         fp := FFEltMinPoly(cp, kc);
         if PolyDeg(fp) > 1 then
            if not KashVersionIsWD then   #old kash2.2 needs that
               AlffInfo("begin unneccessary slow embedding ...\n");
               repeat
                  kp := FF(fp);
                  FFEmbed(kp, FFEltFF(cp));
               until FFEltMove(FFGenerator(kp, k), FFEltFF(cp)) = cp;
               AlffInfo("end unneccessary embedding.\n");
            else
               kp := FF(fp);
               # compute image of generator of kp in FFEltFF(cp)
               # generator of kp is mapped to cp 
               # FFEltFF(cp) gets a "relative extension"
               pg := List(FFEltToList(FFGenerator(kp)), 
                          x->FFEltMove(x, FFEltFF(cp)));
               pg := Sum([0..Length(pg)-1], i->pg[i+1] * cp^i);
               FFEmbed(kp, FFEltFF(cp), pg);
               if not FFEltMove(FFGenerator(kp, k), FFEltFF(cp)) = cp then
                  return Error("cannot embed finite fields as wanted");
               fi;
            fi;   
         else
            kp := k;
         fi;
         yp := FFEltMinPoly(yp, kp);
         yp := Reversed(PolyToList(yp));
         yp := List(yp, a->Poly(kc, Reversed(FFEltToList(a, k))));
         yp := Sum([1..Length(yp)], i->yp[i]*Ys^(i-1));
         
         pp := AlffDivisorGcd(
                       AlffDivisorNum(AlffDivisor(yp)),
                       AlffDivisorNum(AlffDivisor(fp + 0*Ys)) );
         
         if not Length(AlffDivisorPlaces(pp)) = 1 then
            return Error("more/less than one place in the fixed field!!!\n");
         fi;
         D := D + (n * AlffPlaceDeg(p) / AlffDivisorDeg(pp)) * pp;
      od;
      
      if not AlffDivisorDeg(D) = n*2^(m-1) then
         return Error("degree of div in fixed field not n*2^(m-1)!!!\n");
      fi;
      
      Add(DL, D);
   od;
   
   AlffInfo("\n");
   AlffInfo("Unreduced hyperelliptic field is\n", Fs, " of genus ", 
           AlffGenus(Fs), "\n\n");
   
   GASMAN("g");GASMAN("C");
   
   if reduce = false then
      if Length(DL) > 0 then
         return Flat( [Fs, DL] );
      else
         return Fs;
      fi;
   fi;
   
   if Length(DL) > 0 then
      return AlffHyperellipticReduce( Fs, DL );
   else
      return AlffHyperellipticReduce( Fs );
   fi;
end;

