# Complete original compatible maps from a greatest source chart

This internal construction supplies full original compatible maps from a
saturated greatest-chart presentation into an arbitrary original target
presentation. It complements Worker 598's `GlobalChartSourceMaps` construction
in the actual saturated category: here the target need not already be
saturated, so the result can be used before extending a constructed cone.
The proof route and recovery/composition pattern are adapted from that
construction; the compatible original-domain inclusion replaces its
saturated-domain inclusion.

`fromChartPullback` first applies the actual greatest-chart bounded-map
construction into the specified target chart domain. Source saturation
supplies coefficient compatibility. It then composes with the compatible
inclusion of that actual original-chart domain into the target. Every
source chart maps into the chosen target chart.

`fromChartPullback_pullback_top` computes the bounded composite through the
greatest chart of the intermediate domain. Its inclusion pullback is the
original identity restriction, and the source identity restriction is also
an actual bounded identity, so the result is exactly the prescribed map.

`fromChartPullback_eq` recovers any compatible map whose entire source image
lies in that target chart, using its complete greatest-source pullback.
The chart equation and surjectivity of the greatest chart identify the
continuous maps. Restriction naturality recovers every smaller-source
bounded pullback, and compatible strong extensionality concludes equality
of entire maps. `fromChartPullback_comp` computes a full composite whenever
the chosen intermediate chart is admissible for the second map, then uses
this recovery theorem.

Field, space and index universes are independent. Source domain saturation
is explicit; the target is arbitrary. This is a chart-source construction,
not a global pullback or etale base-change theorem. No external statement
is transcribed.
