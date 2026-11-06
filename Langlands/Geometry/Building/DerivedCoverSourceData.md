# Actual derived-cover source data from universal structural inputs

This internal assembly works at arbitrary universe `u` with the actual derived
inclusion and simply connected cover already stored in
`ParahoricBuildingData.zeroDatum`. It neither chooses a replacement ambient group
nor postulates a source building.

`ParahoricBuildingData.DerivedCoverSourceData` bundles valuation-building data on
that actual cover, a forward homomorphism of the original normalizer point
groups, an affine equivalence from the source apartment to the ambient apartment,
exact transport of the original affine roots, equivariance for the original
actions, and lifts of every normalizer in the ambient simply connected image.
It also records that the normalizer map is the map on rational points of the
actual composite of the cover and derived inclusion.

`ParahoricBuildingData.derivedCoverSourceData` constructs this bundle from three
explicit, exact universal inputs:

- `SimplyConnectedDerivedCoverSplitTorusStatement`;
- `DerivedCentralSplitTorusProductStatement`;
- `Langlands.BruhatTits.Cartan.CentralizerValuationComparisonStatement`.

The first input supplies maximal split tori in the derived group and its actual
cover, their two commuting squares, a closed embedding into the ambient torus,
and an isogeny between the covering tori. The already proved
`splitComponentStatement` supplies an actual central split component.
`IsSplitComponent.exists_commFactor_of_isMaximalSplitTorus` factors it through
the given ambient maximal split torus. The second universal input makes the
actual derived/central torus product a central isogeny; its scheme flatness and
surjectivity provide exactly the inputs of the existing valuation pullback.
No surjectivity on rational points is used.

`CentralizerDatum.ofValuationComparison` constructs both actual source
centralizers from closed all-test representability, canonical torus
factorization, and the third universal input. The assembly then reuses
`derivedCoverValuationBuildingData` and all the original affine-root,
normalizer-action, and normalizer-lifting comparisons in
`DerivedCoverBuildingComparison`. The source apartment is the literal
two-stage valuation pullback, including the full V6 compatibility.

`DerivedCoverSourceData.normalizer_map_eq_affineWeylGroup` applies the existing
cover transport theorem to the bundled comparisons. It still requires the exact
`SimplyConnectedFacetFixingStatement`, actual opposite factor pairs for the
source and target tori, and the target apartment axioms. No source apartment
axioms or AS5 are assumed.

The provenance is internal composition of these named Library interfaces and
proved results, without a new independent literature assertion. The three
universal inputs and the facet-fixing and opposite-pair prerequisites are not
proved here. In particular, this construction does not prove
`SimplyConnectedNormalizerAffineWeylStatement`.
