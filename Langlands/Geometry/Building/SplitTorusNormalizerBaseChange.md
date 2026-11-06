# Actual normalizer actions under split-torus field extension

This internal construction compares the existing normalizer actions over
arbitrary fields `k` and `K` in the same arbitrary universe `u`, with an
arbitrary supplied `k`-algebra structure on `K`. It uses the original torus
homomorphism `i : S.toGrp ⟶ G` and its actual scheme pullback.

The pullback of an actual normalizing automorphism witnesses that the actual
extended rational point normalizes the pulled-back homomorphism. The proof
applies base change to the defining conjugation equality, then uses
`baseChange_innerIso_hom` and `rationalExtend_eq_baseChangeBasePoint`.
`normalizerPointsFieldExtend` packages this construction as a group
homomorphism. Its ambient carrier map is exactly `rationalExtend k K G`.
No splitness, affineness, reductivity or maximality is required for this map.

Centralizer points remain centralizer points, by pulling back the identity
automorphism. Consequently `relativeWeylGroupFieldExtend` is the induced map
on the existing quotients of normalizer points by centralizer points.

When the underlying scheme map of `i` is a monomorphism, pullback preserves
that property. Uniqueness of the normalizing automorphism identifies the
chosen automorphism upstairs with the pullback of the chosen original
automorphism. Character pullback then intertwines the actual Weyl actions,
using `characterLattice.baseChange_precomp`.

For a supplied split torus, `splitCocharacterBaseChange` intertwines the
actual real normalizer actions. Tensor induction reduces the proof to
`cocharacterLattice.baseChange_comp` and the automorphism identity.
Quotient induction gives the same compatibility for the actual relative
Weyl group actions. If `G` is affine and locally of finite type, quotient
induction on the root annihilator further shows that
`splitTranslationBaseChange` intertwines the existing reduced normalizer
actions `translationAction`. No root-set or action-compatibility premise
is added.

The provenance is internal: the definitions and proofs compose the published
scheme pullback, conjugation naturality, lattice pullback, tensor extension
and quotient constructions. They introduce no new assertion from original
literature.

This contribution concerns the supplied split torus and its own pullback.
It does not enlarge that torus to a maximal split torus over `K`, construct
compatible root valuations or an apartment map, compare affine translation
terms, or prove `IntegralModel.BuildingComparisonStatement`.
