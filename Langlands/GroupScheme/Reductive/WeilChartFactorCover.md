# The descended factor group over the cover

Namespace `Langlands.GroupScheme.WeilChart`. This internal construction is the ninth step of the
proof of `AffineWeilPairSingleChartDescentStatement`. It shows that the descended factor group
`G' = factorGroup` (module `Langlands.GroupScheme.Reductive.WeilChartFactorGroup`) becomes the
given group `H` after base change to `C`. As a consequence `G'` is reductive with almost simple
geometric fibres.

## Setting

As in `WeilChartWeilIso`: `e : A' ⊗[A] B ≃ₐ[A'] C`, a chart
`P : G_{A'} ≅ AffineWeil.groupScheme A' C H`, factor rigidity `hR`, `H` reductive with almost
simple geometric fibres, `A'` faithfully flat over `A`, the invariance `hinv`, and `G` affine. For
the cover part, `C` carries a `B`-algebra structure with `algebraMap B C b = e (1 ⊗ b)`
(hypothesis `hBC`). For the last two results, `Spec C → Spec B` is étale and surjective.

## Naturality of the chart description

- `diagMap_resBHom`, `chartObjMap χ g`: a map `χ : X ⟶ X'` of `B`-algebras induces a map of chart
  objects (module `Langlands.GroupScheme.Reductive.WeilChartFactorChart`) for the chart maps `g`
  and `χ ∘ g`.
- `resBChart`, `chartMu_lTensor`, `underPointsEquiv_resBHom`: the chart point equivalences and the
  multiplication maps `chartMu` are compatible with `χ`.
- `factorChartEquiv_naturality`: the chart description `factorChartEquiv X g : G'(X) ≃* H(chartObj)`
  (module `WeilChartWeilIso`) is natural in `X`.

## Over the cover

- `coverB B Y` is a `C`-algebra `Y` regarded as a `B`-algebra. `coverChart e hBC Y` is its chart
  map `A' → C → Y`. `diagMap_cover`: the induced map `C → Y` is the structure map of `Y`.
- `chartObjToY` is the identity of `Y`, from the chart object to `Y`. `factorChartEquiv_congr`
  compares the chart descriptions for two equal chart maps.
- `coverEquivB Y : G'(Y) ≃* H(Y)` is natural in `Y` (`coverEquivB_naturality`, through
  `coverBMap`). `coverPointsEquiv` identifies the points of `G'_C = G' ×_{Spec B} Spec C` over `Y`
  with the points of `G'` over `Y` as a `B`-algebra, naturally (`coverPointsEquiv_naturality`).
- `coverTotalEquiv` and `coverNatIso` form the natural isomorphism of point functors `G'_C ≅ H`.
  `coverIso` (**`G'_C ≅ H`**) is reconstructed by `AffinePointComparison.iso`, using
  `isAffine_coverBaseChange`.

## Properties of `G'`

- `factorGroup_isReductive`: `G'` is reductive. This is the Library's reflection of reductivity
  along surjective étale base change (`IsReductive.of_baseChange_of_etale`), applied to `coverIso`.
- `factorGroup_isAlmostSimple`: every geometric fibre of `G'` is almost simple. For a point `t` of
  `Spec B`, choose `s` over `t`. The geometric fibre of `G'_C ≅ H` at `s` is the base change of
  the geometric fibre of `G'` at `t` along an extension of algebraically closed fields
  (`RelativeLevi.geometricFiberBaseChangeIso`). Almost simplicity reflects along field extensions
  (`IsAlmostSimple.of_fieldExtension`).

## Provenance

This is internal. In Conrad, *Reductive group schemes* (2014), proof of Proposition 6.4.4, the
descended group becomes the given group over the étale cover. Its properties (reductive, with
absolutely simple geometric fibres) are then étale local. Here this is proved through the chart
description of the points of `G'`.
