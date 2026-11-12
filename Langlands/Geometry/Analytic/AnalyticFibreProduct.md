# Fibre products of saturated presentations and of analytic spaces

Author: Worker 21.

This module transfers the fibre product of compatible strong maps
(`FibreProductAtlas`, `FibreProductProjections`) to the Library's category of
saturated presentations, and from there to the localized category
`LocalizedCategory` of analytic spaces. Given strong maps `f : X → S` and
`g : Y → S` of saturated presentations whose spaces are Hausdorff, it defines:

- the fibre product `fibreProduct f g`, a saturated presentation;
- the projections `fibreProductFst f g : fibreProduct f g ⟶ X` and
  `fibreProductSnd f g : fibreProduct f g ⟶ Y`.

It proves that the square commutes, as strong maps (`fibreProduct_condition`)
and in the localized category (`localizationFunctor_fibreProduct_condition`).
That the square is a pullback in the localized category is the separate
statement `FibreProductPullbackStatement` (module
`AnalyticFibreProductStatement`).

All declarations lie in `Langlands.Analytic.SaturatedAtlasPresentation`. The
presentations lie in `SaturatedAtlasPresentation.{u, u, u} K`: the Library's
comparison isomorphism `saturationIso` needs equal space and index universes,
and the glued fibre product has its space and indices in `max u w`.

## Original source and derived provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`,
Proposition 1.4.1, printed p.29 / PDF p.26: "The category Φ_k-𝒜n admits fibre
products." Printed p.30 / PDF p.27: "It is easy to see that the canonical
projections Y' → Y and Y' → X' are morphisms of Φ_k-analytic spaces and that Y'
is a fibre product of Y and X' over X in the category Φ_k-𝒜n."

The passage between the categories is derived. It uses the Library's
comparison isomorphisms between a saturated presentation and the saturation of
its original presentation (`saturationIso`), and the saturation of compatible
strong maps (`CompatibleStrongHom.saturationExtension`).

## From strong maps to compatible maps

- `compatibleMap f`: the compatible strong map between the original
  presentations of `X` and `S` whose saturation is
  `saturationIso.hom ≫ f ≫ saturationIso.inv`. It is the Library's
  `originalRestriction` of that composite (`saturationExtension_compatibleMap`).
  Its base map is that of `f` (`compatibleMap_baseMap`).
- `saturatedMap f`: this saturation as a morphism of saturated presentations.
  `saturatedMap_comp_saturationIso`:
  `saturatedMap f ≫ saturationIso.hom = saturationIso.hom ≫ f`.

## The fibre product

- `fibreProduct f g`: the Library's saturation (`ofSaturation`) of the glued
  fibre product presentation `FibreProduct.presentation` of `compatibleMap f`
  and `compatibleMap g`. Its space is the glued space of `FibreProductAtlas`.
- `fstSaturated`, `sndSaturated`: the saturations of the projections
  `FibreProduct.fstHom` and `sndHom`.
- `fibreProductFst f g := fstSaturated f g ≫ saturationIso.hom` and
  `fibreProductSnd f g`, likewise. Their continuous maps are the projections
  `FibreProduct.fst` and `snd` (`fibreProductFst_baseMap`,
  `fibreProductSnd_baseMap`).
- `fibreProduct_condition`: `fibreProductFst f g ≫ f = fibreProductSnd f g ≫ g`.
  Saturation is a functor (`saturationExtension_comp`), so it carries the
  square `FibreProduct.fstHom_comp` of compatible maps to
  `fstSaturated ≫ saturatedMap f = sndSaturated ≫ saturatedMap g`. The
  equations `saturatedMap_comp_saturationIso` for `f` and `g` turn this into
  the stated square.
- `localizationFunctor_fibreProduct_condition`: the same square after the
  localization functor.

## Scope

Not proved here: the universal property of the square in the localized
category (stated as `FibreProductPullbackStatement`), fibre products of
morphisms of the localized category that are not images of strong maps, and
base change of étale morphisms.
