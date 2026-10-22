# Finite fixed-field stages and closure inflation

This internal construction works for every characteristic-zero field `K : Type u`
in an arbitrary common universe `u`, every finite Galois intermediate field `E`
of `AlgebraicClosure K`, and every natural degree `q`.

`finiteGaloisStageCochainIso K E` identifies the actual ordinary cochain complex
of the finite quotient by `finiteGaloisFixingSubgroup K E`, with its actual fixed
unit coefficients, with the ordinary cochain complex of `unitsRepresentation K E`.
It specializes the published `finiteStageCochainIso` using the intrinsic group
and coefficient equivalences constructed in `FixedFieldStages`, and their proved
equivariance. The inverse laws are inherited from that cochain isomorphism.
`finiteGaloisStageCochainIso_homologyMap` identifies its induced map in every
degree with the existing `finiteGaloisStageRelativeIso` by definitional equality.

`finiteGaloisStageRelativeIso_closureInflation` states the pointwise identity
between the existing `finiteStageToContinuous` map and the existing
`closureInflation K E q` applied after the intrinsic stage identification.
The proof applies `finiteStageToContinuous_eq_mapIso` with the genuine continuous
restriction homomorphism and closure-unit inclusion. The quotient restriction
formula is `finiteGaloisStageGroupEquiv_mk`; the coefficient inclusion formula is
`finiteGaloisStageUnitsLinearEquiv_inclusion`. These proved formulas yield the
continuous cohomology equality. Unfolding the definitions identifies the inverse
discrete comparison with `continuousToRelativeEquiv.symm`, and the final continuous
map with `closureContinuousInflation`, exactly as used by `closureInflation`.

This is an internal specialization of the published cochain factorization and
finite-field comparison constructions; it makes no additional literature claim.
No equivalence or map-compatibility hypothesis is left to a caller. The result
does not assert vanishing or absolute degree-two exactness.

Authorship: Worker 54. The intrinsic field and unit identifications are imported
from Worker 68's published `FixedFieldStages` module.
