# Universe-general regular charts on actual affine points

For `k : Type u` with `RCLike k`, `RegularChart k X d` uses the existing actual
`RingPoint k X k` carrier and evaluation topology. Its model is `Fin d → k`,
viewed as a real normed space. The forward coordinates are fractions of global
regular functions with denominators nonzero on the chart source. Every global
regular function pulled back along the inverse chart is real `C∞` on the open
chart target. These are explicit analytic output data; they are neither a
definition of algebraic smoothness nor a theorem constructing charts from it.

`RegularAtlas` selects such a chart containing each point. Its named
`chartedSpace` has exactly these chosen partial homeomorphisms as its atlas.
It introduces no new point type, topology or global charted-space instance.
`ofIsEmpty` handles empty point spaces for every dimension, including zero.
The model has real dimension `d * Module.finrank ℝ k`; the actual real and
complex specializations have dimensions `d` and `2*d`.

`RegularChart.typeZeroEquiv` and `RegularAtlas.typeZeroEquiv` are equivalences
with the Type 0 interfaces. They retain every partial homeomorphism,
numerator and denominator. Their forward and inverse maps are inverse by
structure eta equality. The two charted-space equality lemmas prove that
converting an atlas in either direction preserves the exact charted-space
structure, not just its topology. Thus this extension specializes to the
existing analytic data on exactly the original points.

This file adapts the Type 0 `PointManifold.RegularCharts` interface to an
explicit coefficient universe and adds the conversion equivalences. The
provenance is internal. This file asserts neither existence of an atlas
from algebraic smoothness nor compatibility of arbitrary charts. Those
algebraic-to-analytic and manifold/family assertions are separate exact
targets, `regularChartExistenceStatement` in `General.RegularChartExistence`
and `regularAtlasComparisonStatement` in `General.RegularAtlasComparison`,
proved in `General.RegularChartExistenceProof` and
`General.RegularAtlasComparisonProof`. The existing Type 0 files are unchanged.
