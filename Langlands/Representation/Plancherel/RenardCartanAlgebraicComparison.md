# Algebraic factors and lattice conclusions for the Renard Cartan comparison

This derived helper isolates the algebraic and lattice parts of Task 5309.
It does not prove Cartan coverage or classification for the ambient compact
subgroup or its standard Levi intersections.

The ambient centralizer factors through the fixed actual standard Levi using
`torusCentralizer_le_standardLevi` and
`SubgroupFunctor.IsRepresentedBy.factorHom`. Its composite with the Levi
inclusion is the original centralizer map. Closedness follows from
`IsClosedSubgroup.of_comp`. The represented-centralizer assertion follows
from `SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf` and
`torusCentralizer_comp_comap_of_mono`. Monicity of the same inclusion also
gives the factorization identity for the original torus map.

`positiveRelativeRoots_standardLevi_subset` uses
`relativeRoots_subset_of_factor` and the unchanged cocharacter to retain
the positivity inequality. It requires no assertion of inherited building
data or reductivity of the standard Levi.

The two lattice conclusions implement the proof route of the published
`renardDominantComparison`. They use
`dominantCentralizerLatticeConclusions_of_latticeComparison`,
`finiteIndex_splitValuationImage_of_comparison` and
`bijOn_C0_splitValuationImage_of_comparison`. Finiteness of the ambient
positive roots is `IsSplitTorus.finite_positiveRelativeRoots`; containment
gives finiteness for the Levi positive roots. The centralizer group, torus
factor, valuation and finite-index lattice are unchanged.

These are internal consequences of existing Library results for the
actual-object predicates used by Renard V.3.21–V.3.23 and V.5.1(4),(5).
The original source target and provenance are documented in
`AvailableRenardCartanStatement.md`; no new source theorem is asserted here.

Author: Worker 163.
