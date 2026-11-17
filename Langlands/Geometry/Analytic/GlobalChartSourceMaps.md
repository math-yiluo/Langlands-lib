# Maps from global chart sources

This internal construction extends the existing greatest-chart bounded-map
comparison to an arbitrary saturated target. The field universe, space universe
and chart-index universe remain independent. Both source and target are
saturated presentations over a complete ultrametric normed field.

Given a source chart covering the whole source, a target chart and a bounded
algebra map from its target algebra to the source chart algebra,
`chartSourceMap` first uses `TopChartPresentation.ofTopPullback` to map into the
actual target chart domain, then composes with the actual domain inclusion.
Its image lies in that target chart. Its pullback at every source chart is the
source restriction composed with the prescribed bounded map; in particular its
global source pullback is that exact map. Its ordinary point map is the
corresponding spectrum map.

`chartSourceMap_eq` recovers every full strong map whose image lies in the
chosen target chart from its complete global bounded pullback. It identifies
the continuous maps using the global chart's surjectivity, then uses source
restriction naturality and the existing saturated-source extensionality
theorem to identify all admissible bounded pullbacks.

`chartSourceMap_comp` gives the composition formula with any strong map whose
bounded pullback is admissible on the selected intermediate chart. The result
is the chart-source map prescribed by the full bounded composite. The proof
computes the global pullback using saturated strong composition and applies
`chartSourceMap_eq`.

The construction uses existing chart-domain and saturation APIs only. It
introduces no completed-residue, field-point preservation, finite pushout or
smallness premise, and does not itself prove preservation of categorical
pullbacks.
