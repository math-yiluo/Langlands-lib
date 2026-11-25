# Proof: the glued fibre product is a pullback of analytic spaces

This module proves the published statement
`Langlands.Analytic.SaturatedAtlasPresentation.FibreProductPullbackStatement`
(module `AnalyticFibreProductStatement`) as the theorem
`Langlands.Analytic.SaturatedAtlasPresentation.fibreProductPullback`.

## What is proved

Let `K` be a complete, ultrametric normed field in universe `u`. Let `X`, `Y`,
`S` be saturated presentations in `SaturatedAtlasPresentation.{u, u, u} K`
whose spaces are Hausdorff, and let `f : X ⟶ S`, `g : Y ⟶ S` be strong maps.
Then the glued fibre product `fibreProduct f g` (module `AnalyticFibreProduct`)
with its projections `fibreProductFst f g` and `fibreProductSnd f g` maps under
`localizationFunctor` to a pullback square over `f` and `g` in
`LocalizedCategory`. This is Berkovich 1993, Proposition 1.4.1, in the form
transcribed by the statement module.

## Route

The Library already proves the pullback property for a related
same-universe fibre product, `smallFibreProduct f g` (modules
`FibreProductSmallSquare`, `FibreProductSmallCone`,
`FibreProductLocalizedLimit`). The small fibre product is built from the
local atlas of good chart domains on the shrunk quotient of the same chart
system. This proof does not build the factorization again. It compares the
glued fibre product with the small one, and then applies the Library's
criterion `IsRefinedStrongPullback.isPullback` (module
`LocalizedPullbackDescent`). That criterion asks for three things:

1. the square commutes as strong maps (`fibreProduct_condition`, published);
2. every strong cone `a : T ⟶ X`, `b : T ⟶ Y` with `a ≫ f = b ≫ g` lifts to
   the fibre product after a quasi-isomorphic refinement of the source;
3. the two projections are jointly monic as strong maps.

The proof does not follow the expected route in the statement's Markdown
(calculus of fractions with pair systems). It reuses the published refined
lifts for the small fibre product instead.

### Uniqueness (item 3)

`FibreProduct.presentationHom_ext`: two compatible strong maps `a b : T → P`
into the glued fibre product presentation `P = FibreProduct.presentation f g`
are equal once `a.comp fstHom = b.comp fstHom` and
`a.comp sndHom = b.comp sndHom`. The argument mirrors the published
`FibreProduct.smallHom_ext`. For each source chart `i`, choose a target chart
`J` of `P` that receives the image of `a`. Then `b` also lands in `J`, because
membership in the pair chart range is detected by the two projections
(`mem_range_chart_iff`). Comparing the bounded pullbacks of the two composites
gives equal composites with the two pushout legs, after
`changeMapChart_self`. `AffinoidPushout.hom_ext` then gives
`a.pullback i J = b.pullback i J`. The base maps agree because every point of
`T` lies in some chart, where both base maps are computed through these equal
pullbacks (`chart_comm`). `CompatibleStrongHom.ext_of_pullback` concludes.

`fibreProduct_hom_ext` lifts this to saturated morphisms `a b : T ⟶
fibreProduct f g`. It precomposes with `T.saturationIso.hom` and takes original
restrictions (`StrongHom.saturationExtension_originalRestriction`). It then
transports the projection equalities through
`saturationExtension_comp` and cancels the isomorphisms `X.saturationIso.hom`
and `Y.saturationIso.hom`. Finally it applies `presentationHom_ext` and
cancels `T.saturationIso.hom`.

### Existence (item 2)

`FibreProduct.smallToPresentation` is a compatible strong map from the small
presentation to the glued presentation:

- Its base map is the inverse of the published homeomorphism
  `smallSpaceHomeomorph` onto the shrunk quotient. It sends each small chart
  point to the corresponding point of the glued chart system
  (`smallToSpace_chart`).
- A small index `J` is sent to the atlas index `smallToAtlasIndex J`, which
  records the same good domain as a nonempty pair chart
  (`range_smallToAtlasIndex_rep`).
- The bounded pullback to a glued chart `T` is the published range restriction
  `rangeRestriction f g`. The chart identity is `chart_rangeRestriction`, and
  restriction compatibility is `rangeRestriction_comp`.
- Coherence: write each pullback as the range restriction to
  `smallToAtlasIndex J` followed by the atlas restriction
  (`rangeRestriction_comp`), then apply
  `IndexedAffinoidAtlas.isMapChartChange_restriction`.

`smallToPresentation_comp_fstHom` and `smallToPresentation_comp_sndHom` show
that this map commutes with the projections. The composite pullback is
characterized by `eq_changeMapChart` together with
`isMapChartChange_rangeRestriction_left` (resp. `_right`).

The glued fibre product uses `compatibleMap f`; the small one uses
`geometricCompatibleMap f`. The lemma
`compatibleMap_eq_geometricCompatibleMap` shows they are equal. Both
saturation extensions agree: one by `saturationExtension_compatibleMap`, the
other by naturality of `saturationComparisonNatIso`. Injectivity of
`CompatibleStrongHom.saturationExtensionEquiv` then gives equality.
`exists_smallFibreProduct_comparison` rewrites with this equality and takes the
saturation extension of `smallToPresentation`. The result is a morphism
`β : smallFibreProduct f g ⟶ fibreProduct f g` with
`β ≫ fibreProductFst f g = smallFibreProductFst f g` and
`β ≫ fibreProductSnd f g = smallFibreProductSnd f g`.

`fibreProduct_exists_refinedLift` composes the published
`smallFibreProduct_exists_refinedLift` with `β`.

### Assembly

`fibreProduct_isRefinedStrongPullback` packages items 1–3, and
`fibreProductPullback` applies `IsRefinedStrongPullback.isPullback`.

## Declarations

In namespace `Langlands.Analytic.FibreProduct` (for compatible strong maps
`f : A → C`, `g : B → C` with Hausdorff spaces and all local domains):
`presentationHom_ext`, `smallToAtlasIndex`, `range_smallToAtlasIndex_rep`,
`smallToSpace`, `smallToSpace_chart`, `smallToSpace_subset`,
`smallToSpace_subset_smallToAtlasIndex`, `smallToPresentation`,
`smallToPresentation_comp_fstHom`, `smallToPresentation_comp_sndHom`.

In namespace `Langlands.Analytic.SaturatedAtlasPresentation`:
`compatibleMap_eq_geometricCompatibleMap`, `fibreProduct_hom_ext`,
`exists_smallFibreProduct_comparison`, `fibreProduct_exists_refinedLift`,
`fibreProduct_isRefinedStrongPullback`, `fibreProductPullback`.

All helper declarations are internal steps of this proof. Their mathematical
content is standard: maps into a fibre product are determined by their
projections, and two constructions of the same fibre product are compared.
The source is Berkovich 1993, Proposition 1.4.1, registered as
`berkovich-1993-etale-cohomology` and cited in the statement's Markdown.
