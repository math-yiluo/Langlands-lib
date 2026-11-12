# Disjoint unions of analytic spaces in the localized category

Author: Worker 21.

This module constructs disjoint unions (coproducts) of arbitrary families of
analytic spaces in the Library's category of analytic spaces,
`SaturatedAtlasPresentation.LocalizedCategory`: saturated presentations with
strong maps, localized at quasi-isomorphisms. The input is a family
`X : J → LocalizedCategory.{u, max z v, max z v}` indexed by `J : Type z`. The
underlying space of the disjoint union is the topological sigma type of the
underlying spaces. The construction is needed for Berkovich's induced spaces
`X_{G/H}` (module `InducedAnalyticSpace`). All declarations are in
`Langlands.Analytic.SaturatedAtlasPresentation`.

## Route

1. Every saturated presentation `T` is quasi-isomorphic to a saturated
   presentation without empty original charts.
   `nonemptyReplacement T := saturationFunctor.obj ⟨T.presentation.nonemptyPresentation⟩`
   saturates the subpresentation of the nonempty charts (`AtlasNonemptyCharts`,
   Worker 56). `nonemptyReplacementHom T` is the saturation of the compatible
   subatlas inclusion followed by the comparison isomorphism `saturationIso`.
   Its base map is the identity (`nonemptyReplacementHom_baseMap`), and it is
   a quasi-isomorphism (`isQuasiIso_nonemptyReplacementHom`): saturation
   preserves quasi-isomorphisms
   (`quasiIsomorphisms_saturationFunctor_map_iff`), and the subatlas inclusion
   and `directFromSaturation` are quasi-isomorphisms.
2. For nonempty-chart presentations, `AtlasDisjointUnionStrongMaps` gives a
   coproduct in the category of compatible strong maps. The helpers are
   `sigmaCompatible`, `compatibleInclusion`, `compatibleDesc`,
   `compatibleInclusion_desc`, `compatible_hom_ext`, `compatibleSigmaMap` and
   `compatibleInclusion_map`.
3. Saturation transports it to saturated presentations:
   - `sigmaPresentation T` is the saturation of the disjoint union of the
     nonempty-chart presentations of the family `T`. Its space is
     `Σ j, (T j).presentation.space` (`sigmaPresentation_space`).
   - `sigmaCofan T` has the saturated inclusions as injections, and
     `isColimitSigmaCofan T` shows it is a coproduct of the replacements
     `nonemptyReplacement (T j)`.
   - Descent (`sigmaDesc`, `inj_sigmaDesc`) and uniqueness (`sigma_hom_ext`)
     use that the saturation functor is full and faithful, and the comparison
     isomorphism `saturationFunctorIso Y` of the target.
   - `isQuasiIso_sigmaCofan_desc`: a family of quasi-isomorphisms between
     replacements induces a quasi-isomorphism between the chosen disjoint
     unions. The induced map is the saturation of the componentwise map, a
     quasi-isomorphism by `AtlasDisjointUnion.isQuasiIso_map`.
4. `rightFractionCoproducts K J` packages these data as a
   `Langlands.CategoryTheory.RightFractionCoproducts` structure for the class
   of quasi-isomorphisms. The Library proves that this class has a right
   calculus of fractions (`SaturatedQuasiIsoRightFractions`).
5. The module `RightFractionCoproducts` then shows that the localization
   functor carries these chosen coproducts to coproducts:
   - `localizedSigma X`, the disjoint union of the family `X` of analytic
     spaces;
   - `localizedSigmaCofan X : Cofan X`, with injections
     `(L (π (T j)))⁻¹ ≫ L (inclusion j)`, where
     `T j = localizedObjectEquiv.symm (X j)` is the presentation of `X j` and
     `π` is `nonemptyReplacementHom`;
   - `isColimitLocalizedSigmaCofan X`, the colimit property in
     `LocalizedCategory`.

   The instance `(localizationFunctor).EssSurj` is Mathlib's
   `Localization.essSurj`.

## Original source and provenance

Disjoint unions are used throughout Berkovich's work. The direct motivation is
Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1.2, printed p.2: "X′ the disjoint union ∐_{i∈G/H} X_i, where X_i is a
copy of X identified by an isomorphism f_i : X ⥲ X_i". The construction and
all proofs here are internal and use only the Library's categories and
Mathlib's calculus of fractions. No mathematical claim beyond the proved Lean
statements is made.
