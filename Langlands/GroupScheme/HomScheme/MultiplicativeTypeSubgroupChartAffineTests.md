# Multiplicative-type subgroup charts on affine tests

Author: Worker 872.

`MultiplicativeTypeSubgroupModuli.IsOpenChartOnAffines j` has the same
actual closed-family, relative multiplicative-type and smoothness
fields as `IsOpenChart j`. It requires injectivity only on affine
test schemes and requires the open-subfunctor criterion only when
both the comparison family's base and the further test scheme are
affine.

`IsOpenChartOfAffinesStatement` is the proposition that these affine
conditions imply the full chart condition, over any base scheme and
for every actual family. There is no smoothness or affineness
assumption on the ambient group in this implication. The companion
proof module proves this proposition by Zariski gluing.

This is an internal proof interface, adapted from the published torus
chart interface by replacing the torus predicate with the relative
multiplicative-type predicate. Its mathematical role is to let affine
coordinate chart constructions feed the all-scheme moduli interface.
No chart-existence or representability theorem is asserted here.
