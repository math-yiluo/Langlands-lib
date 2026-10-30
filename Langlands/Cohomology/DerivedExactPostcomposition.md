# Exact postcomposition of actual derived complexes

For abelian categories `C`, `D`, and `E` with their chosen derived categories,
assume `C` has enough injectives. Let `F : C ⥤ D` be additive and let
`P : D ⥤ E` be additive and preserve finite limits and finite colimits.
There are no injectivity assumptions on `F` or `P`, and no requirement
that `D` or `E` have enough injectives. All category, morphism, and
localization universes remain independent.

`DerivedPlus.derivedPostcompIso F P` is a natural isomorphism

```text
(derivedComplex F ⋙ DerivedCategory.Plus.ι) ⋙ P.mapDerivedCategory
  ≅ derivedComplex (F ⋙ P) ⋙ DerivedCategory.Plus.ι.
```

Here `derivedComplex` is the published actual right derived functor applied
to a coefficient object in degree zero. `P.mapDerivedCategory` is Mathlib's
functor on actual derived categories induced by the exact functor `P`.

The construction uses a single injective resolution `I` of the coefficient
object. The published `AcyclicResolution.derivedResolutionIso` identifies
the derived complexes of `F` and `F ⋙ P` with their images of `I`, extended
from natural to integer degrees and localized. Between these two models,
`resolutionPostcompNatIso` uses Mathlib's
`P.mapDerivedCategoryFactors` and
`Functor.mapHomologicalComplexCompIso`. Thus it is the comparison induced
by the termwise composite, with its direction specified by the displayed
isomorphism.

`derivedPostcompIsoOfResolution_hom_naturality` proves compatibility with
every morphism of injective resolutions. Applying this to a lift of the
identity proves independence of the resolution. The components computed
with the chosen resolutions then form `derivedPostcompIso`.
`derivedPostcompIso_hom_app` gives its formula with every injective
resolution, and `derivedPostcompIso_hom_resolution` states its agreement
with the termwise comparison after transport to the resolution models.

This is an internal construction from the published derived-resolution
comparison and Mathlib's exact-functor localization. It uses no new
external mathematical assertion. It supplies no geometric scalar-change
map, affine-open localization, perfect representative, or base-change
theorem for schemes.
