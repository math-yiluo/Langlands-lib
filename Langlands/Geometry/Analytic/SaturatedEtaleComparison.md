# Canonical saturation comparison and the existing étale predicate

Author: Worker 208.

This internal unit compares the actual canonical saturation extension with
the constructed saturation isomorphisms. It proves that the existing
localized `etale` predicate used by `EtaleSite` is exactly the closure of
`localizedFractionEtale` under arbitrary arrow isomorphisms. It does not
prove that the intrinsic fraction property already respects all such
isomorphisms, so the equality of the two properties and composition of the
existing predicate remain separate obligations.

The field `K : Type u` is complete and ultrametric. The field and ambient
space universes `u` and `v` remain independent. Original atlas indices are
in `v`, as in the existing localized étale predicate; no Hausdorff or
compactness assumption is imposed.

## Complete bounded-map naturality

`directFromSaturation_pullback_original_heq` and
`directToSaturation_pullback_original_heq` identify the two comparison
pullbacks at each original chart with the bounded identity, up to the
proved equality of the chosen representative algebra with the original
algebra. Once the representative local domain is identified with the
original whole-chart domain, uniqueness of local-domain inclusions gives
these complete bounded-map equalities.

`saturationExtension_eq_conjugate` identifies the actual canonical
extension of `f : A ⟶ B` with
`(A.saturationIso.hom ≫ f) ≫ B.saturationIso.inv` as strong morphisms.
The proof applies uniqueness of an actual saturation extension. The
conjugate has the same ambient map. Its original-chart pullback is the
original pullback of `f` composed with the two comparison maps, by the
saturated-composition equation. The preceding identity comparisons,
transported through composition of complete bounded maps, recover exactly
that original pullback. Extension uniqueness then proves the whole-map
equality, including every newly admissible bounded pullback.

The selected definition `saturationComparisonNatIso` packages the chosen
`saturationIso` components into a natural isomorphism from the canonical
replacement functor to the identity on the saturated category. Its
naturality follows from the conjugation equality by canceling the target
comparison isomorphism. This supplements the existing objectwise
comparison with its full map equation.

## Predicate comparison

`strongEtale_ofSaturation_iff` shows that for an actual map between
constructed saturations, `strongEtale` agrees with the original
`IsEtaleAllPieces` predicate. Use the conjugation equality and the proved
source and target quasi-isomorphism invariance: the two actual saturation
comparisons are full quasi-isomorphisms.

`etale_map_of_strongEtale` first applies the existing constructor of
localized étale arrows to the canonical extension. Its localized map is
the conjugate of the original mapped arrow, so the existing predicate's
isomorphism invariance cancels the two comparisons.
`etale_localizedRightFraction_of_strongEtale` then precomposes the mapped
numerator by its inverse denominator. These facts give the one-sided
inclusion `localizedFractionEtale_le_etale` for arbitrary localized
objects, using their fixed original-object representatives.

Finally, `etale_eq_isoClosure_localizedFractionEtale` proves an exact
closure equality. In the forward direction the definition of `etale`
supplies an all-pieces strong representative between constructed
saturations. The preceding equivalence and the intrinsic fraction test
place its mapped arrow in `localizedFractionEtale`, retaining the original
arrow isomorphism. In the reverse direction, the one-sided inclusion and
isomorphism invariance of the existing `etale` predicate extend the
inclusion to the whole closure. This is an equality of the original
properties on the actual localization, without modifying either the
site or its target statement.

All results are derived from existing actual comparison families,
original bounded-pullback recovery, full extension uniqueness, and the
included proved quasi-isomorphism invariance. No external theorem
translation or unproved geometric input is used. The unchanged prerequisite
pairs are included for complete dependencies pending their integration.
