# The actual reflection-normalizer Weyl action from explicit AS 4

This internal construction restricts the actual apartment action of
`ValuationBuildingData.reflectionNormalizer` to the existing affine Weyl group.
The homomorphism `reflectionWeylActionOfAS4` requires only the explicit AS 4
condition: every extended affine root, or its double, is an ordinary affine
root. It has the same underlying affine transformation and point action as
`B.apartment.normalizerAffineEquiv` on that subgroup. The field and the actual
group scheme are in arbitrary universe `u`.

The upper inclusion
`reflectionNormalizer_map_le_affineWeylGroup_of_AS4` uses no affine-root-system
or local arrangement hypothesis. Every generator is the action of an actual
opposite factor pair. `NormalizerAffineRootAction` already proves, without
apartment axioms, that its integral coroot is a coroot for the ordinary roots.
AS 4 now places its point functional, or its double, among those roots.
The published `IsCoroot.smul` and `affineReflection_smul` from
`AffineChamberWallComparisonProof` identify the doubled-root reflection with
the original one. The closure defining the reflection-normalizer then gives
the upper inclusion and the restricted homomorphism.

For the lower inclusion
`affineWeylGroup_le_reflectionNormalizer_map_of_locallyFinite`, the ordinary
roots need only satisfy `IsLocallyFiniteReflectionArrangement`: finite spanning
derivatives, nonzero root derivatives, existence of coroots, and pointwise
bounded-root finiteness. Actual opposite factor pairs must also exist for
every nonidentity relative-root point, as expressed by
`RelativeRoot.HasOppositeFactorPairs`. Every ordinary root is an extended
root and therefore a point functional of such a root point. Choose an
opposite pair for that point. Coroot uniqueness for a locally finite
reflection arrangement, proved in `AffineReflectionGalleryGeometry`, identifies
its actual coroot with the coroot specifying the affine Weyl generator.
This realizes every generator in the reflection-normalizer image. AS 4 is
not needed for this lower inclusion.

Combining these two inclusions gives
`reflectionNormalizer_map_eq_affineWeylGroup_of_AS4` and surjectivity of
`reflectionWeylActionOfAS4`. Taking the preimage of the image equality and
applying `Subgroup.comap_map_eq` identifies the full affine-Weyl preimage
with the join of the actual reflection-normalizer and the kernel of the
apartment action.

Finally, `reflectionNormalizer_facet_fixing_of_AS4` applies
`AffineRootSystem.affineWeyl_facet_fixing` through the constructed
homomorphism. An actual reflection-normalizer element preserving a full facet
as a set fixes all its points, assuming only AS 4 and the local arrangement
geometry. This consequence does not require existence of additional
opposite pairs.

This module weakens the assumptions on the existing constructions in
`RootReflectionWeyl` and `ApartmentRootReflections`, using the unconditional
actual action from `NormalizerAffineRootAction`. It is derived from these
published modules and the generic facet-fixing construction; it makes no
additional external source claim. It supplies neither AS 4 nor the local
arrangement geometry nor opposite-pair existence for arbitrary supplied data.
It also supplies no generation theorem for the full simply connected
normalizer. The exact `SimplyConnectedFacetFixingStatement` remains a separate
proof obligation, with all of its premises unchanged.
