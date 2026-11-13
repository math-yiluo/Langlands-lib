# Canonical cohomology pullback and change of the affine base ring

Module `Langlands.AlgebraicGeometry.Modules.CohomologyPullbackBaseRing`.
Author: Worker 134.

## Main result

Let `φ : R ⟶ R'` be a map of commutative rings, `h : Y ⟶ X` a morphism of
schemes over `Spec R'`, `M` an `𝒪_X`-module and `n : ℕ`. Write
`(Over.map (Spec.map φ)).map h` for the same morphism regarded over `Spec R`
through `Spec R' ⟶ Spec R`.

`relativeCohomologyPullback_overMap` proves

```text
relativeCohomologyPullback ((Over.map (Spec.map φ)).map h) M n
    ≫ (relativeCohomologyBaseRingIso φ (Y.hom ≫ Spec.map φ) Y.hom rfl n).hom.app (h^* M)
  = (relativeCohomologyBaseRingIso φ (X.hom ≫ Spec.map φ) X.hom rfl n).hom.app M
    ≫ (ModuleCat.restrictScalars φ.hom).map (relativeCohomologyPullback h M n).
```

So the published canonical pullback `relativeCohomologyPullback` on
`R`-module cohomology agrees, under the published identification
`relativeCohomologyBaseRingIso` of `R`-module cohomology with the
restriction of scalars of `R'`-module cohomology, with the canonical
pullback computed over `R'`. Both pullbacks are the unchanged published
constructions; no hypothesis on `φ`, `X`, `Y`, `h` or `M` is assumed.

## Generic homological part (namespace `Langlands.Cohomology.DerivedPlus`)

`C`, `D`, `E` are abelian with chosen derived categories, `C` has enough
injectives, `G : C ⥤ D` and `H : C ⥤ E` are additive, `P : D ⥤ E` is
additive and preserves finite limits and colimits, and `e : G ⋙ P ≅ H`.

- `plusTermwiseIso G P e`: the natural isomorphism, on bounded below
  complexes `K` of `C`, between `P.mapDerivedCategory` applied to the
  localization of `G(K)` and the localization of `H(K)`. Its component is
  Mathlib's `P.mapDerivedCategoryFactors` followed by `Q` of the termwise
  isomorphism `Functor.mapHomologicalComplexCompIso e`, conjugated by
  `DerivedCategory.Plus.QCompιIso`.
- Instance `isRightDerivedFunctor_rightDerivedFunctorPlus_comp_ι`:
  `H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι`, with the whiskered
  unit, is a right derived functor of `H` followed by localization and
  inclusion. The proof is the argument already used in the Library's
  `exists_acyclicComparison` (Mathlib's derivability structure of injective
  complexes and `isRightDerivedFunctor_of_isIso`).
- `baseChangeTrans G P e : R H ⋙ ι ⟶ R G ⋙ ι ⋙ P.mapDerivedCategory`, the
  natural transformation given by Mathlib's `rightDerivedDesc` applied to
  the inverse of `plusTermwiseIso` followed by the whiskered unit of `G`.
  `baseChangeTrans_fac` is its defining factorization;
  `baseChangeTrans_app_of_isIso` and `inv_unit_comp_plusTermwiseIso_inv`
  compute it on complexes where both units are invertible.
- `derivedComplexIso_inv_baseChangeTrans` computes it at a single object
  through any injective resolution, and `baseChangeTrans_single` proves that
  at a single object `X` it equals the inverse of the Library's
  `derivedCompIso G P e` at `X`. The proof compares both in the resolution
  models using `derivedCompIso_hom_resolution` and
  `resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app`.

## Scheme part (namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`)

- `overMapSectionsIso φ X` is the published
  `relativeGlobalSectionsBaseRingIso` for the factorization
  `((Over.map (Spec.map φ)).obj X).hom = X.hom ≫ Spec.map φ` (by `rfl`);
  it is the identity on sections.
- `overMapSectionsIso_pushforwardSections`: this identification commutes with
  the published `relativePushforwardSectionsIso` for `h` and for
  `(Over.map (Spec.map φ)).map h` (checked on elements; all maps are identities
  on sections).
- `plusTermwiseIso_hom_pullbackSectionsComplexIso` and its inverse form
  `pullbackSectionsComplexIso_plusTermwiseIso_inv`: the termwise comparisons
  commute with the published `pullbackSectionsComplexIso` over `R` and `R'`.
- `relativeDerivedSectionsPullback_overMap`: the published derived pullback
  `relativeDerivedSectionsPullback` over `R` followed by
  `derivedCompIso.inv` equals `derivedCompIso.inv` followed by
  `P.mapDerivedCategory` of the derived pullback over `R'`. Proof: rewrite both
  `derivedCompIso.inv` as `baseChangeTrans` at single objects, unfold the
  definition of `relativeDerivedSectionsPullback`, and move `baseChangeTrans`
  across its four factors using the previous lemmas, the invertibility of the
  units on pushforwards of injective resolutions (published
  `isIso_unit_pushforward_resolution`), and naturality of `baseChangeTrans` for
  `pullbackDerivedAugmentation`.
- `relativeCohomologyPullback_overMap`: take cohomology, using the Library's
  `derivedCompIso_inv_homology`, `mapDerivedCategoryHomologyIso_hom_naturality`
  and `rightDerivedCompIsoOfResolution_baseRingIso`, which identifies the
  classical comparison with `relativeCohomologyBaseRingIso`.

## Provenance

Internal. This is the standard compatibility of derived functors with an exact
change of the target abelian category, applied to the canonical cohomology
pullback. No literature statement is formalized. Everything is derived from
published Library constructions (`relativeCohomologyPullback`,
`relativeDerivedSectionsPullback`, `derivedCompIso`,
`relativeCohomologyBaseRingIso`) and Mathlib's right derived functor API. The
module uses no Picard, abelian-scheme or lifting result.
