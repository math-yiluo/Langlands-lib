# Actual covers by multiplicative-type subgroup charts

Author: Worker 872.

`MultiplicativeTypeSubgroupModuli.HasChartCover G` is the chart-cover
conclusion for one actual group scheme: there are actual closed
multiplicative-type subgroup families over smooth parameter schemes,
each an open chart on all test schemes, whose evaluations cover all
actual same-field points of the subgroup functor.

This is an internal abbreviation of the conclusion of
`MultiplicativeTypeSubgroupModuli.ChartCoverStatement` for one `G`.
It imposes no smoothness or affineness assumption on `G` by itself.
The module imports the published generic `ChartCoverTransport`
operations for comparing all-test ranges, ambient postcomposition
and pushing families across base changes. Those operations have no
torus hypothesis and are reused without modification.

The accompanying base-change, open-extension and noetherian-reduction
modules establish the structural chart-cover operations for the new
multiplicative-type interface. This definition asserts no chart
existence.
