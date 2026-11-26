# Additive Haar measure under the product map and the conjugation chart

The module `Langlands.Analysis.Local.WeylChartMeasures` applies the local change of variables
for additive Haar measure over a nonarchimedean field to the two coordinate maps of
`Langlands.Analysis.Local.WeylChartMaps`. Here `F` is a complete, proper, ultrametric
nontrivially normed field and `R` a finite-dimensional, complete, ultrametric normed
`F`-algebra with its Borel structure.

## Definitions and instances

The coordinate space `Coord F γ` and its two factors are finite dimensional and proper
(`coord_finiteDimensional`, `coord_properSpace`, `range_properSpace`,
`centralizerAlg_properSpace`). `coordHaar γ` is the product of the additive Haar measures
`addHaar` of the two factors, an additive Haar measure on `Coord F γ`
(`coordHaar_isAddHaarMeasure`).

## Results

For `γ` in regular position:

- `exists_productMap_pushforward`: there is `r₁ > 0` such that for every `r ∈ (0, r₁]` the
  product map is a bijection from the closed ball `B` of radius `r` about `0` onto
  `coordCLE '' B`, and the pushforward of `coordHaar γ` restricted to `B` under the product
  map is the pushforward of `coordHaar γ` under `coordCLE`, restricted to `coordCLE '' B`.
- `exists_conjChart_pushforward`: there is `r₂ > 0` such that for every `r ∈ (0, r₂]` the
  conjugation chart is a bijection from `B` onto
  `chartDerivative '' closedBall (chartDerivative⁻¹ 1) r`, and the pushforward of
  `coordHaar γ` restricted to `B` under the chart is the pushforward of `coordHaar γ` under
  `chartDerivative`, restricted to the image of `B`.

Both are instances of `Langlands.Analysis.local_map_restrict_eq_of_hasStrictFDerivAt` (local
restricted pushforward for a map with invertible strict derivative on a proper ultrametric
space), with the strict derivatives `hasStrictFDerivAt_productMap` and
`hasStrictFDerivAt_conjChart`. For the product map, `productMap 0 = 0` turns the image ball
into `coordCLE '' B`.
