# Recovered full and neutral models of fixed building pairs

This internal construction assembles published model and coefficient-action
interfaces. Let `F` be a nonarchimedean local field, `K = inertiaFixedField F`,
and `G` a connected reductive `F`-group. Supply a descended torus that is maximal
split over `K`, KP apartment data `D`, its compatible centralizer datum, and
coefficient stability of `D`.

For two arbitrary points `y₁, y₂` of the actual quotient `D.ReducedBuilding`,
each fixed by every coefficient automorphism of `K/F`,
`recoveredFixedBuildingPairModels` constructs actual full and
neutral models over both integer rings. It uses the published proofs of the
three model-existence inputs:

- `MaximalUnramified.vertexOneStabilizerMaximalBounded`;
- `GroupScheme.maximalBoundedIntegralModel`;
- `IntegralModel.smoothIntersection`.

The conditional helper `recoveredFixedBuildingPairModelsOfVertexInputs` retains
the corresponding three propositions as parameters. The selected construction
discharges them all. There is no local-field hypothesis on `K`, no
common-apartment hypothesis for the points, and no additional smooth-descent
input. Both characteristics and arbitrary field universe `u` are allowed.

## Data and exact recovery

`RecoveredBuildingFixerModels D Y` contains lower and upper
`RelativeComponentModelData`, an `UnramifiedComponentModelRecovery` between
them, and the equality

```
upper.full.integralPoints =
  characterValuationKernel (MaximalUnramified.valuation F) G_K
    ⊓ D.pointwiseFixer Y.
```

The recovery includes actual full and neutral model isomorphisms over the
generic identity and their compatible inclusion square.
`RecoveredBuildingFixerModels.baseChange_full_integralPoints` transfers this
equality to the unramified base change of the lower full model. The selected
definition returns this data for `Y = {y₁, y₂}` by specializing the conditional
classical choice construction to the three published proofs.

## Implemented construction

`exists_smoothBuildingPointModel_of_vertexInputs` uses
`IntegerValuationBuildingData.exists_smul_apartmentMap` to represent each point
separately as `g • apartmentMap x`. The singleton `{x}` is nonempty and every
affine real-valued function on it is bounded above. The published
`exists_smoothFullModel_of_vertexInputs` then constructs its full smooth model,
using the three retained inputs together with the proved
`MaximalUnramified.finiteVertexFixerApproximation` and
`IntegralModel.finiteIndexEnlargement`.

`exists_smoothBuildingPairModel_of_vertexInputs` applies the supplied smooth
intersection assertion to the two singleton models over the actual Henselian
discrete valuation ring `fixedFieldIntegers F`, whose residue field is
algebraically closed. The intersection of the two integral-point groups is
exactly the character kernel intersected with the pointwise fixer of the pair.
This step uses separate apartment representatives and does not establish a
common apartment.

The coefficient-action lemma
`KPApartmentData.rationalConjugate_mem_characterKernel_inf_buildingSubset_iff`
works for any coefficient-fixed subset of the quotient over any field
extension and any invariant valuation. It combines the published character
kernel invariance theorem
`rationalConjugate_mem_characterValuationKernel_iff` with
`galoisQuotientAction_smul_eq_iff`, applied at each fixed point of the subset.

`exists_recovery_of_fixedBuildingSubset` uses this invariance and the published
`IntegralModel.unramifiedSmoothModelDescent` through
`exists_unramified_componentModelRecovery`. The latter recovers the actual
neutral component and inclusion from the full-model isomorphism.
The connected reductive hypothesis gives geometric connectedness of the
generic fibre and its base change. Applying
`IntegralModel.relativeComponentModelDataOfSmooth` to the upper pair model
therefore supplies the component data needed for descent.

## Scope and provenance

Every new assertion is an internal deduction from the named published
interfaces. The unconditional constructor fills the three proposition
parameters with the actual published model proofs: the vertex proof uses the
integer-valued common-apartment and boundedness results over the maximal
unramified field; the maximal-bounded proof uses a stable lattice, schematic
closure and smoothening; and the intersection proof uses diagonal closure and
smoothening. These proof inputs do not consume any of the forbidden
unramified-descent descendant statements in the host task.

This construction generalizes the apartment-subset recovery
interface in `UnramifiedFixedSubsetRecovery` to arbitrary quotient pairs and
uses the already proved smooth descent theorem.

The construction supplies a model in which one may subsequently close a torus
whose units fix the pair. It does not construct a special torus or a common
apartment, and it does not prove
`UnramifiedFixedPairSpecialApartmentStatement`. Obtaining the special torus
and the apartment comparison remains an independent obligation.
