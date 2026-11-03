# Inversion on actual root groups with one positive weight

This derived module isolates the inversion step in the nonmultipliable-root
argument of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Proposition C.2.24(iii), printed pp.621–622 (PDF pp.647–648).
The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`.
The source chooses a torus point over an algebraic closure with character
value `-1`. The lemmas here work on any test scheme where such a point exists;
they do not assert that it exists over the original field.

The internal predicate `RelativeRoot.IsInversionPoint i a s` records that the
given torus point acts by inversion on all points of the actual root subgroup
on that same test scheme. It is a pointwise condition and supplies no
representability, existence, or descent assertion.

`IsWeightVectorCoordinates.act_eq_inv_of_weight_eq_neg_one` proves directly
that the scalar `-1` acts by group inversion in the existing equivariant
vector coordinates. It is valid also in characteristic two.
`conj_eq_inv_of_equivariantVectorQuotient` transports that identity through
an equivariant quotient with trivial actual kernel and an equivariant
map into the ambient group. The quotient is monomorphic by its trivial
kernel, so cancellation suffices. There is no inference of surjectivity
on a group's rational points from an fppf cover.

`subgroup_conj_eq_inv_of_noHigherPositiveRoots` applies this construction to
the actual character-orbit root subgroup. Its hypotheses explicitly retain
the existing semigroup realization, cyclic-root comparison and equivariant
cyclic-filtration statements. Absence of every positive multiple of degree
at least two makes the second filtration term trivial. The first term has
a represented equivariant vector quotient of weight `a`, which gives
inversion on the ambient root point.
`isInversionPoint_of_noHigherPositiveRoots` packages the same conclusion in
`IsInversionPoint`.

This is a conditional helper for the rank-one factorization task. It does
not prove any of the three source structural statements, exclude higher
roots unconditionally, or establish the final rank-one factorization
statement.
