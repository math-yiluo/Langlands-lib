# Reductivity and relative components of the supplied good local model

This internal deduction retains the exact local-field hypotheses and actual
supplied integral model of `BuildingComparisonStatement`. If its generic group
and its full actual residue pullback are connected reductive, then
`IntegralModel.isReductive_of_reductive_localField` proves that the original
group scheme over the valuation ring is reductive. Smoothness is imported from
the published `isSmooth_of_reductive_localField`; it is not added as a premise.

The proof first transports generic reductivity through the supplied
`genericIso`, then applies the published actual-field-point reflection theorem
to the fraction-field and residue-field pullbacks. The fraction-field point
lands at the generic point. For the residue pullback, the inverse image of the
field's zero ideal is the valuation ring's maximal ideal, by the kernel formula
for the actual residue quotient. Every point of the DVR spectrum is generic
or closed, so all residue-field fibres are connected reductive. Their actual
geometric pullbacks are pseudo-reductive by field-extension preservation.
Together with smoothness and the original model's affineness, this supplies
exactly the published `IsReductive` predicate.

`hasConnectedFibres_of_reductive_localField` extracts connectedness of every
actual scheme-theoretic fibre. More generally, the identity of any reductive
group scheme represents its all-test relative identity component: every
residue-field group is connected, so its identity component has the entire
underlying space; every test point therefore satisfies the fibre-image
criterion. The identity morphism is an open immersion and every test point
factors through it.

`relativeComponentData_of_reductive_localField` constructs the published
`RelativeComponentModelData` using the original supplied `M` as both the full
and neutral model. Both generic identifications are literally `M.genericIso`,
and their inclusion is the identity of `M.group`. It supplies the proved
smoothness, fibre connectedness and all-test relative-component property.
Consequently this construction introduces no replacement for the original
model or for its integral-point image.

The provenance is internal. The proof uses the published DVR spectrum
classification, `LocalSmoothness`, the actual fibre and field-extension
theorems in `Reductive.GenericSpreadingAssembly` and `Reductive.BaseChange`,
the existing relative-component definitions, and Mathlib topology. No new
external assertion is assumed.

This result constructs the specified relative-component data for the given
model. It does not identify that model with a canonical building model, prove
any stabilizer identity, construct building data or a metric, or prove
`BuildingComparisonStatement`.
