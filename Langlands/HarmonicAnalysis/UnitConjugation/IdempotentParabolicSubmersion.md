# The conjugation submersion for an idempotent parabolic

Let \(e\) be an idempotent of the algebra \(A\). Write \(M\) for its
centralizer, \(U=eA(1-e)\) for the upper corner and \(L=(1-e)Ae\) for the
opposite corner. In a finite-dimensional normed algebra over a complete
nontrivially normed field, `parabolicConjugation` is the map on additive
coordinates that sends \((g,Y,Z)\) to \(g(Y+Z)g^{-1}\) for \(g\) a unit,
\(Y\in M\) and \(Z\in U\). It uses `Ring.inverse` on the first coordinate.

`idempotentParabolicSubmersion` proves `IdempotentParabolicSubmersionStatement`.
At such a triple, if \([Y,\cdot]\) is surjective on the off-diagonal summand
\(U\oplus L\), the map has a surjective strict Fréchet derivative.

## Proof

`exists_parabolic_commutator_add` first constructs a preimage of any
direction \(W\) under \((T,V,S)\mapsto [T,Y+Z]+V+S\), where \(T\in L\),
\(V\in M\) and \(S\in U\). The projection onto \(L\) commutes with left
and right multiplication by \(Y\). Projecting a preimage of the \(L\)
component of \(W\) under \([Y,\cdot]\) and changing its sign therefore
gives \(T\) with \([T,Y]\) equal to that component. The products \(TZ\)
and \(ZT\) are diagonal, so the proof subtracts \([T,Z]\) from the
diagonal component of \(W\) to obtain \(V\). It takes \(S\) to be the
upper component of \(W\).

The strict derivative is obtained by the two multiplication rules and
the strict derivative of `Ring.inverse` at \(g\). On the increment
\((gT,V,S)\), the derivative is \(g([T,Y+Z]+V+S)g^{-1}\).
Applying the algebraic preimage construction to \(g^{-1}Wg\) gives
the desired derivative value \(W\).

## Source

This strict derivative computation gives the submersion step for a
pushforward proof of local summability in the idempotent case of
Harish-Chandra's parabolic descent. In the setting of Lemma 1.13, the
descent test integral averages over conjugation of the sum of the Levi
and nilradical coordinates. The two corners here are the Lie algebras
of the unipotent radical and its opposite for the parabolic defined by
\(e\). See Harish-Chandra, *Admissible invariant distributions on
reductive p-adic groups*, University Lecture Series 16, 1999,
§1.4, pp. 9–10.
