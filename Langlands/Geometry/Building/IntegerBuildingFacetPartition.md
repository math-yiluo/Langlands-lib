# Full facets of the actual integer-valued quotient form a partition

This internal deduction proves `IntegerBuildingFacetPartitionStatement` for
an arbitrary field `k : Type u`, an integer-valued valuation, and the published
`IntegerValuationBuildingData v G`. The facets are exactly its existing
`IsFacet` subsets of the same reduced quotient, defined as translated images
of full affine facets. Each quotient point lies in exactly one such subset.
There is no local-field, characteristic or apartment-axiom hypothesis.

Connected reductivity and maximal splitness, supplied by the data, give actual
opposite factor pairs through `rootRankOneFactorization`. The published
`KPApartmentData.mem_or_two_smul_mem_affineRoots_of_oppositePairs` then proves
AS4. The normalizer preserves the original ordinary roots by
`normalizerAffineEquiv_mem_rootStabilizer`, without AS5. These are the only
parts of the full apartment-axiom package needed here.

The proof specializes the published sharp-fixer constancy on an affine facet
and reads the original `ApartmentQuotient.mk_eq_mk_iff` relation at a shared
point. Its normalizer witness gives the same coordinate change throughout
that entire facet: the remaining sharp-fixer factor fixes each of its points.
Consequently any two translated facet images meeting at that point coincide,
using the partition by affine-root signs in the apartment. Quotient covering
supplies existence. The proof follows the published local-field deductions in
`ApartmentFacetConstruction` and `BuildingFacetPartition`, but applies them
at arbitrary fields by deriving precisely their needed hypotheses from the
data instead of imposing a local-field instance.

`IntegerValuationBuildingData.BuildingFacet` is the subtype of the same
existing `IsFacet` subsets. `buildingFacetAt` chooses the unique containing
facet; its membership and containment characterization are proved. No new
point carrier or group action is introduced.

This constructs no integral model, residue parabolic correspondence, maximal
invariant facet or special apartment. The exact prescribed-point split-torus
target `UnramifiedFixedPointSplitTorusStatement` remains to be proved.
