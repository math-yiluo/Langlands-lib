# Recovering actual integer-building facets from their quotient images

Module `Langlands.BruhatTits.IntegralModels.UnramifiedIntegerFacetImageRecovery`.
All declarations allow arbitrary universe `u` and both characteristics.

This is an internal consequence of published full-building zero-fixer geometry,
Henselian special-fibre image recovery and the parabolic correspondence through
a unipotent quotient. It concerns the actual maximal-unramified integer-valued
building, without assuming that its field is a nonarchimedean local field.

## Data and explicit inputs

Let `F` be a nonarchimedean local field, `H` an affine group scheme over
`UnramifiedClosure F`, `E : UnramifiedZeroDatum F H`, and
`C : MaximalUnramified.BuildingData F H`. The supplied building data include
connected reductivity, a maximal split torus, apartment and centralizer data,
and omega compatibility. Let `R` be a Henselian local domain with fraction field
`UnramifiedClosure F` and algebraically closed residue field, and let
`M : IntegerFacetModelData C R` be an actual family of relative component
models with generic-identity incidence maps. Fix a full facet `Fc` and supplied
quotient data `Q` for its neutral special fibre.

`UnramifiedIntegerFacetImageRecoveryStatement` retains four assumptions:

* Every full facet `J` has the neutral integral-point characterization
  `(M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val`.
* `Q.IsReductiveQuotient` holds for the supplied quotient data.
* For every facet incident above `Fc`, its neutral integral points contain the
  congruence subgroup of the target neutral model at `Fc`.
* Every corresponding actual neutral special-fibre image in the target is
  parabolic.

Under these assumptions, the actual map `M.incidentParabolicImage Fc Q` takes
values in parabolic subgroup functors, is injective, and reflects and preserves
reverse incidence: its image at `J` is contained in its image at `J'` if and
only if `C.FacetPrecedes J'.val J.val`. Every image is the all-test range of
the actual schematic-image inclusion. The theorem
`unramifiedIntegerFacetImageRecovery` proves this Prop-valued statement.

## Implemented proof

`UnramifiedZeroDatum.buildingZeroFixer_le_iff_facetPrecedes` first identifies
zero-fixer containment with reverse incidence for full facets. Containment
implies incidence by the published
`facetPrecedes_of_buildingZeroFixer_le`, applied to the whole nonempty facets.
The converse uses `pointwiseFixer_le_of_facetPrecedes`. This uses neither a
no-inversions assumption nor a restriction from a downstairs building.
`neutral_integralPoints_le_iff_facetPrecedes` then substitutes the supplied
neutral integral-point formula.

`unramifiedIncidentParabolicImage_isParabolic_and_comap` applies the published
`RelativeComponentModelHom.parabolicReductiveImage_and_comap` to each actual
model morphism. It proves parabolicity of the actual quotient image and recovers
the original special-fibre image as its full inverse image under the quotient
projection. This helper needs only a local ring, valid quotient and special-fibre
image parabolicity.

For `unramifiedIncidentParabolicImage_le_iff`, containment of quotient images
gives containment of their full inverse images. The preceding helper identifies
these with the actual special-fibre images. The published
`specialFibreImage_le_iff_integralPoints_le` uses Henselian smooth lifting,
algebraically closed residue and the two explicit congruence containments to
recover containment of generic integral points. The full-facet zero-fixer
comparison then gives reverse incidence. The other direction is the published
`incidentParabolicImage_le`, which follows from actual model-map composition.
Applying the comparison in both directions and facet-incidence antisymmetry
proves `unramifiedIncidentParabolicImage_injective`.

The companion import cleanup in `GenericRootFixerIntersection` changes only its
provider of generic apartment injectivity to `GenericApartmentInjection` and
corrects the provider name in its Markdown. Its theorem statements and proofs
are unchanged. This avoids passing through the maximal-unramified wrapper
`MaximalUnramifiedApartmentInjective`, whose imports contain the unramified
building-descent statements of `UnramifiedBuildingDescentReduction`; neither
`GenericRootFixerIntersection` nor this module imports them.

This module does not construct the model family, prove its neutral integral-point
formula, supply congruence containment or special-fibre image parabolicity, or
prove attainment of all parabolics. In particular it establishes neither the
full facet-parabolic bijection nor the fixed-point split-torus theorem
`UnramifiedFixedPointSplitTorusStatement`.
