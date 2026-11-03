# Minimal pseudo-parabolic subgroups over a field

Author: Worker 1335.

This module defines `Langlands.GroupScheme.IsMinimalPseudoParabolicSubgroup`
for an actual homomorphism `i : P ⟶ G` of group schemes over
`Spec (CommRingCat.of k)`, for any field `k : Type u` and arbitrary universe
`u`.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The discussion after Theorem C.2.3 and Proposition C.2.4, printed p.594
(PDF p.620), use minimality among the pseudo-parabolic subgroups defined
over the ground field. Theorem C.2.5, printed p.595 (PDF p.621), states
rational conjugacy for these minimal subgroups. The present module supplies
the minimality predicate needed to state that theorem; it proves no
conjugacy or existence assertion.

`IsMinimalPseudoParabolicSubgroup i` is the conjunction of
`IsPseudoParabolicSubgroup i` with the following condition: for every actual
group scheme `Q` over the same field and every homomorphism `j : Q ⟶ G`
that is pseudo-parabolic, containment of `SubgroupFunctor.range j` in
`SubgroupFunctor.range i` implies equality of these two subgroup functors.
The imported pseudo-parabolic predicate requires that the ambient `G` is
smooth, connected and affine; it expresses a closed subgroup as a represented
fppf-local product of a dynamic parabolic and a ground-field unipotent
radical.

This all-test formulation implements the source's subgroup minimality.
For the closed subgroup homomorphisms in question, all-test image
containment and equality record scheme-theoretic subgroup containment and
equality. It uses the same minimality convention as the published
`Rational.MinimalParabolic` module, with the distinct pseudo-parabolic
predicate. It tests every relative scheme, including nonreduced and
nonaffine tests, and imposes no infinitude or perfection condition on the
field.

Three elementary consequences unpack the definition.
`isPseudoParabolicSubgroup` extracts the first conjunct.
`isClosedSubgroup` applies the existing closedness consequence of that
conjunct. `range_eq_of_le` applies the second conjunct to a supplied
pseudo-parabolic homomorphism and containment of all-test images.
These proofs do not show that the source `P` is smooth or connected, or that
minimal pseudo-parabolic subgroups exist.
