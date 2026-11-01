# Natural transformations of derived source squares

This internal construction compares the actual mapped injective resolutions
and the existing `DerivedPlusSource.derivedMap` construction. It will be used
to transport the geometric inverse-image section map to the étale-restriction
section map.

Let `C`, `D`, and `E` be abelian categories with independent object and
morphism universes. The functors `T, U : C ⥤ D` are additive, preserve
homology, and preserve injective objects. A natural transformation
`θ : T ⟶ U` is arbitrary; it need not be invertible.

For any specified actual injective resolution `I` of `X`,
`mapResolutionNatTrans T U θ I` is an actual
`InjectiveResolution.Hom` from the constructed mapped resolution under `T`
to the constructed mapped resolution under `U`, lifting `θ.app X`.
Its chain map is the degreewise application of `θ`. The augmentation
condition follows from the proved degree-zero formula for both mapped
augmentations and naturality of `θ` at `I.ι.f 0`. No existence assumption
on resolutions of other objects or derived categories is needed for this
construction.

Given additive `F : C ⥤ E`, `G : D ⥤ E`, and
`τ : F ⟶ T ⋙ G`, `imageResolutionSquare_comp_natTrans` proves
that the extended square for `τ`, followed by `G` of this actual
resolution map, equals the extended square for
`τ ≫ Functor.whiskerRight θ G`. The proof combines extension with
composition, then checks the equality in each degree.

With enough injectives in `C` and `D` and independently chosen
`HasDerivedCategory` universes for `C`, `D`, and `E`,
`derivedMap_whiskerRight` proves the equality of actual natural
transformations

```text
derivedMap F T G τ ≫ whiskerRight θ (derivedComplex G)
  = derivedMap F U G (τ ≫ whiskerRight θ G).
```

The proof evaluates the existing arbitrary-resolution formula
`derivedMap_comp_map_ofResolutions` using the constructed compatible
resolution map, applies the preceding extended-square equality, and
identifies the result with `derivedMap_app` for `U`. The comparison is
proved rather than supplied as input.

The provenance is internal categorical infrastructure, using the published
`DerivedPlusSourceFunctoriality`, `DerivedPlusSource`, and
`DerivedComparison` constructions and Mathlib's degreewise map of
homological complexes. This module does not assert geometric
specialization, compact support, equivariance, or the Harris comparison.
