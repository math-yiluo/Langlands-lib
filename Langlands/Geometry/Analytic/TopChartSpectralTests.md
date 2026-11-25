# Localized tests on greatest charts

This module derives the comparison from the Library's greatest-chart
pullbacks, source quotient equivalence and definition of `IsNear`.

`localizedTopTargetHomEquiv` identifies the complete strong maps into
a target with a greatest chart with the corresponding localized
morphisms. It composes the greatest-chart Hom equivalence for the
source quotient with the comparison of that quotient to the
localization. Its forward map is localization on strong maps.

`isNear_greatestChart_iff` applies when the source and target both have
greatest charts. For a test triple on the greatest target chart, the
localized nearness relation is equivalent to the spectral bound on the
difference of the two bounded pullbacks in the greatest source chart.
The result allows different source and target spaces and arbitrary
complete ultrametric fields.

In the forward direction, the common quasi-isomorphic denominator in
`IsNear` pulls the two strong maps back to the two given numerators,
using injectivity of `localizedTopTargetHomEquiv`. Every point of the
source lifts across the denominator's underlying homeomorphism and
lies in a chart of the denominator source. Composition of bounded
pullbacks identifies the bound at that chart point with the bound at
the original spectrum point. In the reverse direction, the greatest
charts cover their respective entire spaces. Restriction maps send
the bound on the greatest source chart to each source chart. The two
strong maps are therefore `StrongNear`, giving `IsNear` with the
identity denominator.

This comparison translates test triples on whole affinoid charts into
the spectral estimates used on fibre-product patches for
`CompactCompatibleTupleConesStatement` (proved as `compactCompatibleTupleCones`
in `Cohomology/AnalyticQuasiEtaleGlobalComparison/CompactTupleConeAssembly`).

The common chart-coverage lemma is `range_greatestChart_eq_univ`.
