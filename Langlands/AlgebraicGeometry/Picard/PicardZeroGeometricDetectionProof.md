# Geometric-point detection for actual rigidified Picard-zero families

This module proves the exact published proposition
`Langlands.AbelianScheme.PicardZeroGeometricDetectionStatement.{u}`.
It is an internal compatibility proof for the existing geometric-fibre
predicate and actual relative rigidified pullback. No additional literature
theorem is asserted.

The forward implication specializes the published `picardZeroPullback` to
the exact slice morphism `Over.homMk s rfl` with source
`Over.mk (s ≫ T.hom)`.

For the reverse implication, fix an algebraically closed field `K` in
universe `u` and an actual map `s : Spec K ⟶ T.left`. The hypothesis gives
the geometric Picard-zero predicate on the actual pulled-back family over
`Spec K`. The published
`isTranslationInvariant_of_isGeometricallyPicardZero` then gives translation
invariance on its abelian scheme itself. That lemma tests the geometric
predicate at the identity of `Spec K`, uses `fibreTranslationIso` to compare
translation with restriction, and reflects the resulting bundle
isomorphism along the identity-base-change projection using
`LineBundle.isoOfPullbackIso`.

The inverse of `GroupScheme.baseChangeCompIso T.hom s A.toGrp` is an actual
group-scheme homomorphism from the iterated fibre `(A_T)_s` to the direct
base change `A_(s ≫ T.hom)`. Its projection to `A` is given by
`baseChangeCompIso_inv_fst`; its parameter projection follows from its
slice equation. The private coordinate lemma checks that this comparison,
followed by the direct relative-space symmetry and the actual relative
space map, equals the original fibre projection followed by the original
relative-space symmetry. It proves equality by both pullback coordinates.

`geometricPointPullbackLineBundleIso` turns this equality into an
isomorphism of actual line bundles using `LineBundle.pullbackComp`.
Forgetting the rigidification of the relative pullback gives precisely
pullback of the original underlying bundle along the relative space map.
Thus the isomorphism compares the bundle of the specified actual
rigidified pullback with the original fibre bundle, rather than an
arbitrarily chosen isomorphic family.

Finally, `GroupScheme.isTranslationInvariant_pullback` transports
invariance along the comparison homomorphism. Its published proof uses
`translation_hom` to intertwine translations by corresponding sections.
`isTranslationInvariant_of_iso` applies the bundle comparison to obtain
the required invariance on the original fibre. Repeating this for every
`K` and `s` is exactly `IsPicardZeroFamily A L`.

The proof retains arbitrary `S` and `T`, including nonreduced parameter
schemes, the universe parameter `u`, every algebraically closed field in
that universe, and every actual geometric-point map. It adds no
transport, projectivity, representability, dual-scheme, or openness
hypothesis and proves no openness or representability result.
