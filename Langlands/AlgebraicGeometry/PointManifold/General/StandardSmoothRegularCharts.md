# Universe-general regular charts on standard-smooth actual affine point spaces

This module adapts the published `PointManifold.StandardSmoothRegularCharts` implementation by Worker 362
to `PointManifold.General`, with an explicit arbitrary coefficient universe
`u` and `k : Type u`. Worker 1650 made this universe extension. It uses the
published actual `RingPoint` carrier and evaluation topology, and leaves the
existing target and all its imported definitions unchanged. The construction
places no positive-dimension or point-nonemptiness premise on its input.

This internal construction removes the split-variable convention from the submersive presentation chart. It assumes only algebraic standard smoothness of relative dimension `d` for the actual coordinate algebra of an affine scheme over an `RCLike` field, and supplies a `RegularChart` containing each actual point.

For the injective dependent-variable map of a finite submersive presentation, the variables are the disjoint sum of its complement and its relation indices. The complement has cardinality `d`, because the presentation dimension is the number of variables minus the number of relations. An equivalence from `Fin d` to this complement reindexes the presentation to variables `Fin d ⊕ σ`. The reindexed dependent-variable map is the second inclusion; Mathlib's presentation reindexing preserves the Jacobian unit. The proved `RegularChart.ofSubmersivePresentation` then gives the exact actual-point chart and source membership.

`exists_regularChart_of_standardSmooth` proves this existence. `RegularChart.ofStandardSmooth` chooses the resulting chart, and its source-membership theorem records that it contains the chosen point. This proof includes zero dimension and empty relation indices and places no nonemptiness assumption on the actual point space. Its provenance is internal: finite set decomposition and cardinal arithmetic applied to the pinned Mathlib algebraic standard-smoothness definition, followed by the existing split submersive chart construction.
