# Closed reference tori in the neutral model of a building pair

This internal construction records the raw integral torus and common chart
needed for integral conjugacy in the model of a pair of building points.
All fields and rings lie in arbitrary universe `u`; there is no
characteristic restriction.

`IntegralPairApartmentReference D M y₁ y₂` contains a translating point
`q`, coordinates for both endpoints in `q · D.apartmentMap`, a closed
integral split torus of `M`, a commutative generic source isomorphism,
and the exact generic equation identifying its map with the conjugated
original apartment torus. Its `subset_range` lemma gives the pair's
coverage by that chart.

The existing `map_translatedApartmentTorus_kernel_le_oneFixer` from
`Langlands.BruhatTits.IntegralModels.UnramifiedPairApartmentTorus` proves that the
image of the
character-valuation kernel of the original torus, conjugated by `q`,
belongs to the character kernel of the ambient group and fixes every
point of any subset of the translated chart. The proof uses
`IntegerValuation.map_mem_characterValuationKernel` and
`map_torusUnits_smul_apartmentMap`, followed by the group action identity
for conjugation.

For maximal-unramified building data `B` and supplied component model
data `N`, `exists_neutralPairApartmentReference` assumes that the
character-kernel fixer of the pair is contained in `N.full.integralPoints`.
It uses the published `MaximalUnramified.commonApartments` to choose
the common chart and the preceding kernel containment to apply
`SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded`.
The maximal-unramified integer ring is a discrete valuation ring with
algebraically closed residue, and the normalized valuation is one on
its units. The resulting integral split torus has geometrically
connected fibres. `RelativeIdentityComponent.factor` therefore maps it
to the actual neutral representative. Closedness follows from
`IsRelativeIdentityComponent.isClosedSubgroup_of_comp`. The component
inclusion's exact generic square preserves the original generic
identification. `neutralPairApartmentReference` chooses these data.

For supplied lower component data
`N : RelativeComponentModelData ↥𝒪[F] F G`, the construction
`N.neutralPairReference` applies this result to the actual coefficient
extension of `N`, with ambient model `N.neutral.baseChangeUnramified`.
It retains the explicit equality identifying
`N.full.baseChangeUnramified.integralPoints` with the character-kernel
fixer of the pair. Its other inputs are the connected reductive original
group, maximal splitness of the original apartment torus after unramified
extension, and the supplied compatible centralizer datum. No existence
of lower component data or full-model equality is asserted here.

`N.neutral_baseChange_integralPoints_le_fixingSubgroup` proves that every
integral point of that same neutral ambient fixes both endpoints, under
the same full-model equality. It uses the component inclusion and that
equality. No common-apartment hypothesis is needed for this fixation
lemma.

The provenance is derived from the published common-apartment theorem,
bounded split-torus closure, connected-source component factorization,
coefficient functoriality of component models, and the supplied full integral-point
equality for the pair. This module does not construct the descended
target torus containing a prescribed split subtorus and does not prove
the fixed-pair special-apartment statement
`UnramifiedFixedPairSpecialApartmentStatement` that it serves; that statement
is proved as `unramifiedFixedPairSpecialApartment` in
`Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentProof`.
