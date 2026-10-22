# Derived complexes in the bounded below derived category

Author: Worker 13. This module is internal derived infrastructure built only
on Mathlib.

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C`
has enough injectives. Categories and morphisms have independent universes.
Mathlib's derived categories are chosen by instances
`[HasDerivedCategory.{w} C]` and `[HasDerivedCategory.{w'} D]`, with
independent universes `w` and `w'`; Mathlib's `HasDerivedCategory.standard`
provides such a choice. Mathlib defines the right derived functor
`F.rightDerivedFunctorPlus` on the bounded below derived categories
`DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`. This module evaluates it at
objects of `C` and identifies the result with injective resolutions and with
the classical derived functors `F.rightDerived n`.

## Extension by zero

Mathlib's `HomologicalComplex.extend` extends a complex along an embedding of
complex shapes, with zero objects outside the image.

- `extendXMapIso F K i` compares the terms of the extension of the image
  `F(K)` with the images of the terms of the extension of `K`. In the image of
  the embedding both are `F` of a term of `K`, and the isomorphism is the
  identity. Outside it both are zero objects, since `F` preserves zero
  morphisms and hence zero objects.
- `extendXMapIso_hom_d` proves that these isomorphisms commute with the
  differentials, by cases on the two indices.
- `mapExtendIso F K e` is the resulting isomorphism of complexes from the
  extension of `F(K)` to `F` applied to the extension of `K`.

These hypotheses only require zero objects and zero morphisms, and `F` to
preserve zero morphisms.

## The derived complex

- `resolutionPlus R` is Mathlib's integer-indexed extension
  `R.cochainComplex` of an injective resolution `R` of `X`, as an object of
  `CochainComplex.Plus C`. It is strictly concentrated in degrees `≥ 0`.
- `derivedComplex F` is `DerivedCategory.Plus.singleFunctor C 0` followed by
  `F.rightDerivedFunctorPlus`: the object placed in degree zero, then derived.
- `singleIsoOfResolution R` identifies `X` in degree zero with the
  localization of `resolutionPlus R`. The map is Mathlib's quasi-isomorphism
  `R.ι'`, which becomes invertible in the derived category. The isomorphism is
  pulled back along the fully faithful inclusion of the bounded below derived
  category.
- `isIso_rightDerivedFunctorPlusUnit_app` proves that the unit of the right
  derived functor is invertible at `resolutionPlus R`. The unit is a composite
  of components of natural isomorphisms and of the homotopy-category unit,
  which Mathlib shows invertible at complexes with injective terms.
- `derivedComplexIso F R` is the resulting isomorphism between
  `(derivedComplex F).obj X` and the localization of `F` applied to
  `resolutionPlus R`.

## Cohomology

- `homologyResolutionIso F R n` identifies the degree `n` cohomology of the
  derived complex, for an integer `n`, with the degree `n` homology of `F`
  applied to `R.cochainComplex`. It uses Mathlib's
  `DerivedCategory.homologyFunctorFactors`.
- `homologyIso F R n`, for `n : ℕ`, continues with `mapExtendIso`, Mathlib's
  `extendHomologyIso` and `InjectiveResolution.isoRightDerivedObj`. It
  identifies the degree `n` cohomology of `(derivedComplex F).obj X` with
  `(F.rightDerived n).obj X`.
- `isZero_homology_of_neg` proves that the cohomology vanishes in negative
  degrees. There the term of `R.cochainComplex` is zero, hence so is its image
  under `F` and the homology.

The isomorphisms are objectwise and depend on the chosen resolution; their
naturality in `X` is not stated.

## Provenance and scope

This is derived infrastructure, not a definition from the literature. Harris,
*Galois properties of cohomological automorphic forms on GL(n)* (1999),
Proposition 4.4, printed p.309, takes `Ext` in smooth representations against
compactly supported cohomology. Its proof, printed p.310, computes that
cohomology by complexes of smooth projective modules. Worker 13 read these
passages in the original. Worker 3's published
`Langlands.Cohomology.HyperextDegenerationStatement` formulates the
degeneration step with an object of Mathlib's derived category. This module
supplies such objects for any left exact functor with enough injectives on its
source. No spectral sequence, boundedness above, or comparison with
projective complexes is asserted.

Source registration:
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

The module imports only Mathlib.
