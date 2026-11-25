# Actual quotient-fixed subsets and compatible segment models

This internal supporting module proves
`Langlands.BruhatTits.IntegralModels.UnramifiedQuotientSegmentModelsStatement.{u}`
by `unramifiedQuotientSegmentModels`, for arbitrary universe `u` and in both
characteristics. It compares two supplied upper integral models, one for a closed
segment in the original apartment quotient and one for its endpoint pair, and
recovers both from one lower model, including their relative identity components.
The statements concern the actual quotient action and actual integral-point image
subgroups.

## Inputs and conclusion of the packaged statement

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` its actual
maximal unramified extension, and `A = fixedFieldIntegers F`. Let `G` be a connected
reductive `F`-group scheme. The statement retains an `F`-source commutative group
scheme `T` and a map `iT : T.toGrp ⟶ G` whose actual base change to `K` is a maximal
split torus. It also retains the supplied `KPApartmentData` `D`, actual
`CentralizerDatum` `C`, full integer-valuation omega compatibility `h6`, and
`GaloisStable` datum `hD` for these same inputs.

Take two points `x,y` of `D.ReducedBuilding`, each fixed by every automorphism
`K ≃ₐ[F] K` under `galoisQuotientAction`. There is no fixed-coordinate hypothesis.
Common apartments `hc` are derived by
`MaximalUnramified.hasCommonApartments_of_apartment hG hiT D C h6`.
The set `D.chosenSegment hc x y` is the image of the previously constructed
closed-interval interpolation in this quotient; no metric interpretation is used.

Supply `E,P : RelativeComponentModelData A K G_K`. These data include actual
smooth full and neutral integral models, the neutral inclusion, connected neutral
fibres and the assertion that the neutral model represents the full model's
relative identity component. Assume the exact full integral-point image formulas

- `E.full.integralPoints` is the intersection of the character valuation kernel
  for `MaximalUnramified.valuation F` with the pointwise fixer of the chosen segment;
- `P.full.integralPoints` is the same character kernel intersected with the
  pointwise fixer of `{x,y}`.

Then there is an actual full-model isomorphism
`e : E.full.Iso P.full (Iso.refl _)`. Its generic identification is the identity on
the original `G_K`. The induced actual neutral-model isomorphism
`E.neutralIso P e` commutes with both neutral inclusions:

`(E.neutralIso P e).iso.hom ≫ P.inclusion.hom = E.inclusion.hom ≫ e.iso.hom`.

The original neutral integral-point image subgroups are literally equal.
Moreover, there is one
`L : RelativeComponentModelData ↥𝒪[F] F G` with both
`Nonempty (UnramifiedComponentModelRecovery L E)` and
`Nonempty (UnramifiedComponentModelRecovery L P)`.
Each recovery contains actual full and neutral isomorphisms from the corresponding
unramified base changes of `L`, identity generic identifications, and the
coefficient-pullback inclusion square. The same lower `L` occurs in both packages.
Their published recovery API also provides exact upstairs image equalities and
downstairs inverse-image formulas; these follow from the packages rather than
being extra hypotheses here.

## Supporting lemmas and implemented proof

`KPApartmentData.pointwiseFixer_chosenSegment_eq_pair` proves equality of the
original pointwise-fixer subgroups over any field, under connected reductivity,
maximal splitness and common apartments. Extensionality reduces the equality to
`mem_pointwiseFixer_chosenSegment_iff` from `ApartmentQuotientSegment`; membership
in the fixer of the endpoint pair is exactly fixation of both endpoints.

The existing
`KPApartmentData.rationalConjugate_mem_characterKernel_inf_buildingSubset_iff`
from `UnramifiedFixedBuildingPairRecovery` works over an arbitrary field extension `k → K`, with any valuation on `K` and a
coefficient automorphism preserving that valuation. A supplied quotient subset
`Y` is pointwise fixed by every coefficient automorphism. The lemma proves that
membership in the intersection of its pointwise fixer with the character
valuation kernel is invariant under the specified rational coefficient
conjugation. The proof separates the two subgroup conditions: published character
kernel invariance handles the first, and `galoisQuotientAction_smul_eq_iff` plus
actual fixation of each point of `Y` handles the second. No nonemptiness,
boundedness or choice of fixed apartment coordinates is needed.

The existing `exists_recovery_of_fixedBuildingSubset` in the same module
specializes this argument to the actual
maximal unramified extension. It assumes geometric connectedness of `G` and a
supplied component model `E` with the exact full image formula for a pointwise
coefficient-fixed subset. The normalized valuation is coefficient-invariant by
`MaximalUnramified.valuation_galois`. The previous lemma proves full-image
stability. The published theorem `IntegralModel.unramifiedSmoothModelDescent`
discharges the smooth descent premise of
`exists_unramified_componentModelRecovery`, which constructs the lower model
and its full and neutral recovery. Thus this lemma has no supplied smooth-descent
statement as a hypothesis. Existence of the upper model remains supplied.

`exists_segment_pair_modelRecovery` first uses the fixer equality and the two
exact image formulas to identify the full integral-point images of `E` and `P`.
`IntegralModel.isoOfIntegralPointsEq` constructs `e`, using
`IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F`
and both full models' smoothness. Published relative-component functoriality gives
`neutralIso_hom_comp` and `neutral_integralPoints_eq`.

Every point of the chosen segment is coefficient-fixed by
`galoisQuotientAction_chosenSegmentPoint_eq_of_endpoints_fixed`. Apply
`exists_recovery_of_fixedBuildingSubset` to `E` to obtain a lower `L` and recovery
`r`. Compose `r.fullIso.iso` with `e.iso`. Functoriality of generic base change,
`e.generic_comm` and `r.fullIso.generic_comm` verify that this composite is still
generic over the identity. Finally
`UnramifiedComponentModelRecovery.ofFull L P` recovers `P` and its actual neutral
component from that composite. This construction is why one lower model suffices.

For the packaged theorem, connected reductivity supplies affine smoothness and
connectedness of `G`; `G.geometricallyConnected_of_connected` then supplies
geometric connectedness. `hG.baseChange_of_algebraicExtension` supplies connected
reductivity of `G_K`. The already derived `hc` and all original inputs are passed
to `exists_segment_pair_modelRecovery`.

## Provenance and scope

This is an internal composition of published Library mathematics, with no new
external source claim. Its direct imports are `ApartmentQuotientSegment`,
`UnramifiedFixedBuildingPairRecovery`, `IntegralModel.UnramifiedSmoothDescentProof`,
`IntegralModel.FixedFieldExtension`, and `GroupScheme.GeometricConnectedness`.
The integral-point comparison uses the published smooth extension and integral
model isomorphism APIs; neutral comparison uses
`RelativeComponentFunctoriality`. These are ordinary imports by Lean name.

The upper models and both exact full image formulas remain supplied. This module
constructs no upper segment model, residue kernel or parabolic-image comparison,
Gamma-facet correspondence, residue-torus lift, or maximal `F`-split torus. It
does not establish a metric or geodesic comparison or locate the prescribed point
in a special apartment. It does not prove
`UnramifiedFixedPointSplitTorusStatement`; `unramifiedFixedPointSplitTorus`
(module `Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusProof`)
proves it without importing this module. No unramified building-descent
statement or theorem consuming one is used as a proof input.
