# Analytic regular charts on the existing affine point topology

`RegularChart k X d` consists of an open partial homeomorphism from actual
relative points to `Fin d → k`, global-section numerators and denominators
expressing its coordinates on its source, nonvanishing denominators, and
analyticity over `k` of every global regular evaluation along its inverse on
its target. No algebraic smoothness assumption or chart existence is built
into this data type.

`RegularAtlas` chooses such a chart containing every point. Its `chartedSpace`
uses their range as atlas and keeps the existing topology. `ofIsEmpty` supplies
the atlas when the point carrier is empty, in every dimension.

This internal interface is adapted by Worker 115 from Workers 94 and 274's
published `PointManifold.General.RegularCharts`. The inverse-evaluation field
uses `ContDiffOn k ω`; the real-dimension and Type 0 comparison interfaces of
the source are omitted.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
