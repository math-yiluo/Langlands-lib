# Naturality of the cohomology of derived complexes

Author: Worker 61. This module is internal derived infrastructure. It imports
`Langlands.Cohomology.ExtendMap`, which reuses Worker 13's published
`Langlands.Cohomology.DerivedPlus` unchanged.

## Setting

The setting is that of `Langlands.Cohomology.DerivedPlus`. `F : C ⥤ D` is an
additive functor between abelian categories, and `C` has enough injectives.
Derived categories are chosen by `[HasDerivedCategory.{w} C]` and
`[HasDerivedCategory.{w'} D]`, and all universes are independent. For an
injective resolution `R` of `X` and `n : ℕ`, that module defines
`homologyIso F R n`. This isomorphism goes from the degree `n` cohomology of
the derived complex `(derivedComplex F).obj X` to `(F.rightDerived n).obj X`.
It is built from the resolution `R` alone, and its naturality in `X` is not
stated there. This module proves that naturality. It then packages the
isomorphisms as a natural isomorphism of functors on `C`.

## Extension by zero

- `extendXMapIso_hom_mapX` proves that the termwise comparison `extendXMapIso`
  commutes with the maps `HomologicalComplex.extend.mapX` that a morphism of
  complexes induces on the extended terms. In the image of the embedding both
  comparisons are identities. Outside it the source is a zero object.
- `mapExtendIso_hom_naturality` proves that `mapExtendIso F K e` is natural in
  `K`. Given `φ : K ⟶ L`, it intertwines the extension of `F(φ)` with `F`
  applied to the extension of `φ`. The inverse identity is the existing
  `Langlands.Cohomology.extendMapIso_hom_naturality` from `ExtendMap`.

The hypotheses are those of `mapExtendIso`: zero objects and zero morphisms,
and `F` preserving zero morphisms.

## Naturality for a morphism of injective resolutions

Fix `f : X ⟶ Y`, an injective resolution `I` of `X` and `J` of `Y`, and a
morphism of resolutions `φ : InjectiveResolution.Hom I J f`. That is Mathlib's
cochain map `φ.hom : I.cocomplex ⟶ J.cocomplex` compatible with `f` in
degree zero.

- `resolutionPlusMap φ` is Mathlib's integer-indexed extension `φ.hom'`, as a
  morphism `resolutionPlus I ⟶ resolutionPlus J` of bounded below complexes.
- `ι_map_singleIsoOfResolution_hom` writes the image of
  `singleIsoOfResolution R` in the unbounded derived category as the
  composite of isomorphisms that defines it.
- `singleIsoOfResolution_hom_naturality` proves that `singleIsoOfResolution`
  intertwines `f` in degree zero with the localization of
  `resolutionPlusMap φ`. The proof applies the faithful inclusion
  `DerivedCategory.Plus.ι`. It then uses the naturality of each isomorphism
  in that composite and Mathlib's `InjectiveResolution.Hom.ι'_comp_hom'`.
- `derivedComplexIso_hom_naturality` proves that `derivedComplexIso`
  intertwines `(derivedComplex F).map f` with the localization of `F`
  applied to `resolutionPlusMap φ`. It uses the previous lemma and the
  naturality of Mathlib's unit `F.rightDerivedFunctorPlusUnit`, inverted at
  the two resolutions.
- `homologyResolutionIso_hom_naturality` proves that `homologyResolutionIso`
  intertwines the map on degree `n` cohomology, for `n : ℤ`, with the map that
  `F(φ.hom')` induces on degree `n` homology. It adds the naturality of
  Mathlib's `DerivedCategory.Plus.QCompιIso` and
  `DerivedCategory.homologyFunctorFactors`.
- `homologyIso_hom_naturality_of_hom` proves, for `n : ℕ`, that
  `homologyIso` intertwines the map on degree `n` cohomology of derived
  complexes with `(F.rightDerived n).map f`. It adds
  `Langlands.Cohomology.extendMapIso_hom_naturality` and Mathlib's
  `HomologicalComplex.extendHomologyIso_hom_naturality` and
  `InjectiveResolution.isoRightDerivedObj_inv_naturality`.

The four preceding naturality lemmas carry `@[reassoc]`; the expansion
lemma `ι_map_singleIsoOfResolution_hom` does not.

## Arbitrary resolutions and the natural isomorphism

- `descHom f I J` is the morphism of injective resolutions over `f` whose
  cochain map is Mathlib's chosen lift `InjectiveResolution.desc f J I`.
  Its compatibility in degree zero is Mathlib's
  `InjectiveResolution.desc_commutes_zero`.
- `homologyIso_hom_naturality F f I J n` is the naturality square for any
  injective resolutions `I` of `X` and `J` of `Y`, with no morphism of
  resolutions given. Explicitly,
  `(DerivedCategory.Plus.homologyFunctor D n).map ((derivedComplex F).map f) ≫
  (homologyIso F J n).hom = (homologyIso F I n).hom ≫ (F.rightDerived n).map f`.
  It is the previous lemma applied to `descHom f I J`.
- `homologyNatIso F n` is the natural isomorphism
  `derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n ≅
  F.rightDerived n` for `n : ℕ`. Its component at `X` is
  `homologyIso F (injectiveResolution X) n`, using Mathlib's chosen
  resolution.
- `homologyNatIso_hom_app F n R` proves that the component at `X` equals
  `(homologyIso F R n).hom` for every injective resolution `R` of `X`. This is
  the naturality square for `f = 𝟙 X` with the resolutions
  `injectiveResolution X` and `R`. So the isomorphism does not depend on the
  resolution used to compute its components.

## Provenance and scope

This is derived infrastructure, not a definition from the literature. That
the cohomology of the derived functor applied to an object is the classical
right derived functor, naturally in the object, is standard homological
algebra. Here it is obtained by combining Mathlib's bounded below derived
functor with Mathlib's `Functor.rightDerived` through the comparisons of
`Langlands.Cohomology.DerivedPlus`. No literature source is cited for it. Its
purpose in the Harris framework is the route to the long exact sequence of
right derived functors and to the comparison of acyclic resolutions with right
derived functors. The derived-category homology sequence is stated for
morphisms of `DerivedCategory`. Its maps must be identified with
`(F.rightDerived n).map f`, and `homologyNatIso` provides this identification.

The generic extension comparison declarations formerly in
`Langlands.Cohomology.DivisibleSystem.InvariantComparison` now live unchanged
in [`Langlands.Cohomology.ExtendMap`](ExtendMap.md). In particular,
`extendMapIso e F K` is `(DerivedPlus.mapExtendIso F K e).symm`, so the
existing `extendMapIso_hom_naturality` gives exactly the inverse-naturality
identity used by this module. Integration reuses that declaration and omits
the duplicate `DerivedPlus.mapExtendIso_inv_naturality`. The forward-oriented
termwise and complex identities above remain as reviewed. Neither this
module nor `ExtendMap` imports the representation-specific divisible-system
modules.

Not provided here: connecting morphisms, the long exact sequence of
`F.rightDerived`, and any statement in negative degrees beyond the vanishing
already proved in `Langlands.Cohomology.DerivedPlus`.
