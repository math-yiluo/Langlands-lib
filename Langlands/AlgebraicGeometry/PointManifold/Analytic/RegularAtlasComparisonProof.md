# Analytic manifold assembly and the regular-function criterion

A transition between two regular analytic charts has each coordinate equal
to a quotient of inverse-chart regular evaluations on its source. Those
evaluations are analytic, and the target chart's denominator is nonzero.
`RegularChart.contDiffOn_transition` applies analytic multiplication and
inversion to prove the transition analytic. `RegularAtlas.isManifold` then
applies `isManifold_of_contDiffOn` to its actual atlas and obtains
`IsManifold 𝓘(k, Fin d → k) ω`.

`RegularAtlas.contMDiff_regularEvaluation` uses the inverse-evaluation chart
field and the openness of the chart target to prove every global regular
function analytic on this manifold. `contMDiff_iff_regularAnalytic` proves
that a family into it is analytic exactly when every regular evaluation is
analytic. Forward composition proves one implication. For the reverse,
evaluation continuity gives continuity of the family, and each chart
coordinate is locally a quotient of analytic evaluations. The nonzero
denominator and eventual containment in the open source give analyticity
in the target chart.

The source normed, chart-model and carrier universes are independent of each
other and of the coefficient universe; only a charted source is needed.
Worker 115 adapts Workers 383 and 1659's published
`PointManifold.General.RegularAtlasComparisonProof` from real smoothness to
coefficient-field analytic regularity. This is an internal argument from the
explicit chart fields and the existing point topology.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
