# Analytic charts for standard-smooth affine algebras

For a finite submersive presentation the complement of the image of its
injective dependent-variable map has cardinality `d`, by the relative-dimension
identity. Splitting the variables into this complement and the dependent
variables and identifying the complement with `Fin d` reindexes the
presentation to `Fin d ⊕ σ` with dependent map `Sum.inr`.

`exists_regularChart_of_standardSmooth` applies the split presentation chart
to obtain a regular analytic chart containing every specified actual point.
`RegularChart.ofStandardSmooth` chooses one and its source lemma records the
same membership. The only algebraic premise is standard smoothness of relative
dimension `d` of the actual coordinate algebra; no analytic input is assumed.

This internal adaptation by Worker 115 follows Workers 362 and 1650's published
`PointManifold.General.StandardSmoothRegularCharts` finite reindexing proof,
with the analytic chart construction in place of its real smooth counterpart.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
