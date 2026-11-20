# Localized maps from an affinoid spectrum into a chart

`LocalizedAffinoidChartFactorizationStatement` identifies any localized
map from a small affinoid spectrum whose image lies in a specified target
chart with the chart map of a unique bounded algebra map. The field and
space universes are independent. The theorem
`localizedAffinoidChartFactorization` proves the statement over complete
ultrametric normed fields.

Use the universal property of the analytic domain of the chart to lift
the given map. The chart is the greatest chart of its domain's subspace
atlas, so the lifted map has a strong representative on the original
source. Compose with the strong domain inclusion. The source's retained
whole-spectrum chart recovers the bounded map of this strong composite
into the chosen target chart. Faithfulness of localization and the
complete pullback on that whole-spectrum chart give uniqueness.

The module also proves compatibility with changing to a containing
chart, using the actual restriction of its algebra. These are internal
consequences of the existing analytic domain universal property,
greatest-chart comparison and complete strong chart maps.
