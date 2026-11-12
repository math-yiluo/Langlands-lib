# Rational point comparison for a covering field isomorphism

This internal adapter for Task 5428 identifies the existing
`coveringPointsMap` with rational extension followed by the given group map.
The algebra structure on the second field is induced by the ring equivalence.
No valuation or affine group hypothesis is required for these facts.

`baseChangeSectionHom_eq_rationalExtend` specializes
`GaloisPointComparison.rationalExtend_hom_eq_baseChangeSectionHom` to this algebra
structure. Substitution into the definition gives
`coveringPointsMap_eq_rationalExtend`.

`coveringPointsMap_bijective` applies
`baseChangeSectionHom_bijective_of_isIso` to the scheme isomorphism induced by
the field equivalence, then composes with the bijection `isoPointsEquiv`
induced by the supplied group-scheme isomorphism. In particular the covering
map is surjective, as needed to compare apartments in the final building
comparison. This is derived from the Library's point and pullback
constructions; it adds no new geometric hypothesis.

`coveringPointsEquiv` bundles this bijective homomorphism as a multiplicative
equivalence. Its forward map is definitionally `coveringPointsMap`, as recorded
by `coveringPointsEquiv_apply`.
