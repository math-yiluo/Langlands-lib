# Rank-one torus descent across a Galois extension of odd degree

`RankOneTorusOddDegreeDescentStatement` concerns an affine commutative group
scheme \(Q\) over a field \(k\) and a finite Galois extension \(L/k\) of odd
degree. If \(Q_L\) is isomorphic to \(\mathbb G_{m,L}\), then every character
of \(Q_L\) is fixed by \(\operatorname{Gal}(L/k)\), and \(Q\) is isomorphic to
\(\mathbb G_{m,k}\).

## Proof

`rankOneLattice_fixed_of_odd_card` starts with a representation on a
\(\mathbb Z\)-module linearly isomorphic to \(\mathbb Z\). After conjugating by
that linear equivalence, the endomorphism representing an element \(\sigma\)
is multiplication by an integer \(a\), its value at \(1\). For the odd order
\(n\) of the group, \(\sigma^n=1\) gives \(a^n=1\). The odd power map is
injective on \(\mathbb Z\), so \(a=1\).

`rankOneTorusOddDegreeDescent` applies this calculation to
`characterLattice.galoisRepresentation`. Precomposition by the splitting
isomorphism identifies the character lattice of \(Q_L\) with that of
\(\mathbb G_{m,L}\), and `gmEndEquiv` identifies the latter with \(\mathbb Z\).
The splitting isomorphism itself, viewed as a character, is therefore fixed.
`galoisInvariantLattices` supplies a character over \(k\) inducing it under the
canonical base-change identification of \(\mathbb G_m\).
`isIso_of_baseChange` reflects the induced isomorphism along the fpqc field
cover.

## The degree-seven application

For a subgroup \(P\leq\operatorname{Gal}(L/k)\) of order seven,
`rankOneTorus_descent_fixedField_card_seven` applies the statement over
\(E=L^P\). The fixed-field degree formula gives \([L:E]=7\), so the action
of \(\operatorname{Gal}(L/E)\) on the rank-one character lattice is trivial
and \(Q\) splits over \(E\). The companion lemma
`rankOneTorus_cocycle_isTrivial_fixedField_card_seven` uses
`Cocycle.isTrivial_of_isSplitTorus_overField` to give a coboundary on the same
cover \(\operatorname{Spec}L\to\operatorname{Spec}E\).

This is the split-quotient step of the type \(E_8\) case of
Platonov–Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8,
Proposition 6.21, printed p. 376 (PDF p. 386). In that application \(Q\) is
the supplied affine quotient \(T_E/S\) with
\(Q_L\simeq\mathbb G_{m,L}\). The lemmas use that isomorphism as a hypothesis.
