# Compatible localized maps into a greatest chart

`localizedGreatestChartHomEquiv` recovers the unique compatible strong map on
the original source when the target has an original chart containing all its
charts. The ambient and chart-index universes agree. The proof uses the two
saturation comparisons in `LocalizedSaturationEquivalence` and the
greatest-chart Hom equivalence of `TopChartSpectralTests`. The original
greatest chart still covers the whole space after saturation. Commutativity of
the localization square identifies the forward map with localization on
compatible strong maps.

`greatestChartPullback` takes the bounded pullback of the recovered strong map
on an original source chart. It acts as the identity on the greatest chart for
an identity arrow. For composition through a greatest intermediate chart, the
unique compatible representatives compose and the bounded pullbacks compose in
reverse order.

These are internal consequences of the localization and saturation
comparisons. They let function tests for varying-field maps use the given
greatest chart and its presented algebra.
