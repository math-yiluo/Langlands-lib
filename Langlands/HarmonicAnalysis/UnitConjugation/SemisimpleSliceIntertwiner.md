# Intertwiners on a semisimple Lie algebra slice

Let \(A\) be a finite-dimensional algebra over a complete nontrivially normed
field \(F\), with compatible algebra norm. For \(S\in A\) write \(B=C_A(S)\)
and \(W=[S,A]\). Both left and right multiplication by \(B\) preserve \(W\).
For \(X,Y\in B\), `sliceIntertwiner X Y` is the endomorphism of \(W\) given by
\(T_{X,Y}(a)=Xa-aY\).

Assume \(A=B\oplus W\). The restriction of \(\operatorname{ad}(S)\) to \(W\)
is injective because its kernel in \(A\) is \(B\). It is therefore bijective.
The endomorphism \(T_{X,Y}\) depends linearly on the pair \((X,Y)\), so its
determinant is continuous. Nonvanishing at \((S,S)\) gives a neighborhood of
\(S\) whose square lies in the nonvanishing locus. Moreover, for
\(u,v\in B^\times\), the linear automorphism \(a\mapsto uav^{-1}\) conjugates
\(T_{X,Y}\) to \(T_{uXu^{-1},vYv^{-1}}\). Consequently the square of the
\(B^\times\)-saturation of that neighborhood still lies in the nonvanishing
locus. `semisimpleSliceIntertwiner` constructs the resulting open invariant
slice.

For \(X,Y\) in this slice, suppose \(Xa=aY\) in \(A\). Decompose \(a=b+w\) with
\(b\in B\) and \(w\in W\). Then \(Xb-bY\in B\) and \(Xw-wY\in W\), and their
sum vanishes. Injectivity on \(W\) gives \(w=0\).
`mem_centralizer_of_intertwiner` proves this implication even when the
intertwiner \(a\) is an arbitrary algebra element. In particular an ambient
unit conjugating two slice elements commutes with \(S\).

This is an associative-algebra calculation for semisimple descent in
\(\mathrm{GL}_1(A)\). Harish-Chandra's *Admissible invariant distributions on
reductive p-adic groups* (AMS, 1999), Corollary 2.3, printed pp. 14–15, uses
invertibility of the diagonal operator \(\operatorname{ad}(Y)\) transverse
to the centralizer. Lemma 2.8, printed p. 16, uses the local separation of
semisimple conjugates in the slice. The two-variable calculation gives
control of the transporters of all pairs in an open slice.
