/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The total right derived functor of an exact functor is `mapDerivedCategory`

An exact functor `F : C ⥤ D` between abelian categories induces a functor
`F.mapDerivedCategory : DerivedCategory C ⥤ DerivedCategory D` directly, by applying `F`
levelwise (`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`). When the abelian
category `C` moreover has K-injective resolutions, `F` also has a total right derived
functor `F.rightDerivedFunctor` computed via K-injective resolutions
(`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`). This file
shows that the two constructions agree:

- `Functor.rightDerivedFunctorIsoMapDerivedCategory`: the canonical isomorphism
  `F.rightDerivedFunctor ≅ F.mapDerivedCategory`, obtained from uniqueness of right
  derived functors: since the comparison `F.mapDerivedCategoryFactorsh` is an
  isomorphism, `F.mapDerivedCategory` is *itself* a right derived functor of
  `F.mapHomotopyCategory ⋙ Qh`.
- `Functor.isIso_rightDerivedFunctorUnit`: consequently, the unit of the right derived
  functor of an exact functor is an isomorphism everywhere (not only on K-injective
  complexes).

From this compatibility we derive, still for exact functors, the isomorphisms expressing
that right derivation commutes with the constructions preserved by `mapDerivedCategory`
(themselves in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
`Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso` and
`Functor.mapDerivedCategoryHomologyFunctorIso`):

- `Functor.rightDerivedFunctorHomologyFunctorIso` and
  `Functor.singleFunctorCompRightDerivedFunctorIso`: the commutation of the total right
  derived functor with the homology functors and with the single-degree embeddings.
- `Functor.rightDerivedFunctorCompIsoOfExact`: the composition isomorphism
  `R(F ⋙ G) ≅ RF ⋙ RG` for *exact* `F` and `G`. This is the exact-functor counterpart of
  `Functor.rightDerivedFunctorCompIso` of
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, which holds
  for arbitrary additive functors but takes `F.PreservesKInjectiveComplexes` instead of
  exactness.
- `Functor.rightDerivedFunctorCompMapDerivedCategoryIso`: the composition isomorphism
  `R(F ⋙ G) ≅ RF ⋙ D(G)` for an arbitrary additive `F` and an *exact* `G`: right deriving a
  composite whose second factor is exact amounts to right deriving the first factor and
  applying the second levelwise.

The functoriality of `rightDerivedFunctor` in natural isomorphisms is *not* repeated
here: `Functor.rightDerivedFunctorNatIso` of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` already
provides it for arbitrary additive functors.

This is the right-derived counterpart of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`.
Note the asymmetry in the hypotheses: left derivation via K-flat resolutions requires the
source category to carry a monoidal structure with functorial flat resolutions, while
right derivation via K-injective resolutions only requires
`CategoryTheory.Abelian.HasKInjectiveResolutions`.

-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Abelian Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

section Compatibility

variable [HasKInjectiveResolutions C]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The functor `F.mapDerivedCategory` induced by an exact functor `F` is a right derived
functor of `F.mapHomotopyCategory ⋙ Qh`, with unit the inverse of the comparison
`F.mapDerivedCategoryFactorsh`: the unit is an isomorphism, and `Qh` is a localization
functor for quasi-isomorphisms. -/
instance isRightDerivedFunctor_mapDerivedCategory :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh

/-- For an *exact* functor `F` between abelian categories, the total right derived
functor computed via K-injective resolutions is canonically isomorphic to the functor
`F.mapDerivedCategory` induced by applying `F` levelwise. Indeed, since
`F.mapDerivedCategoryFactorsh` is an isomorphism, `F.mapDerivedCategory` is itself a
right derived functor of `F.mapHomotopyCategory ⋙ Qh`, and right derived functors are
unique up to canonical isomorphism. -/
noncomputable def rightDerivedFunctorIsoMapDerivedCategory :
    F.rightDerivedFunctor ≅ F.mapDerivedCategory :=
  rightDerivedUnique F.rightDerivedFunctor F.mapDerivedCategory F.rightDerivedFunctorUnit
    F.mapDerivedCategoryFactorsh.inv (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

@[reassoc (attr := simp)]
lemma rightDerivedFunctorIsoMapDerivedCategory_hom_fac :
    F.rightDerivedFunctorUnit ≫
        Functor.whiskerLeft DerivedCategory.Qh
          F.rightDerivedFunctorIsoMapDerivedCategory.hom =
      F.mapDerivedCategoryFactorsh.inv := by
  simp [rightDerivedFunctorIsoMapDerivedCategory]

/-- The unit of the total right derived functor of an *exact* functor is an isomorphism
everywhere: the right derived functor is computed by applying the functor levelwise, with
no resolution needed. -/
instance isIso_rightDerivedFunctorUnit : IsIso F.rightDerivedFunctorUnit := by
  have : IsIso (F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        F.rightDerivedFunctorIsoMapDerivedCategory.hom) := by
    rw [F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (Functor.whiskerLeft DerivedCategory.Qh
      F.rightDerivedFunctorIsoMapDerivedCategory.hom)

/-- The total right derived functor of an exact functor commutes with the homology
functors: the canonical isomorphism
`H^n(-) ⋙ F ≅ F.rightDerivedFunctor ⋙ H^n(-)` of functors `DerivedCategory C ⥤ D`. -/
noncomputable def rightDerivedFunctorHomologyFunctorIso (n : ℤ) :
    DerivedCategory.homologyFunctor C n ⋙ F ≅
      F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D n :=
  F.mapDerivedCategoryHomologyFunctorIso n ≪≫
    isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.symm
      (DerivedCategory.homologyFunctor D n)

/-- The total right derived functor of an exact functor commutes with the single-degree
embeddings: the canonical isomorphism
`(-)[0] ⋙ F.rightDerivedFunctor ≅ F ⋙ (-)[0]` of functors `C ⥤ DerivedCategory D`. -/
noncomputable def singleFunctorCompRightDerivedFunctorIso :
    DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ≅
      F ⋙ DerivedCategory.singleFunctor D 0 :=
  isoWhiskerLeft (DerivedCategory.singleFunctor C 0)
      F.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    F.mapDerivedCategorySingleFunctor 0

end Compatibility

section Composition

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]

/-- The composition isomorphism
`(F ⋙ G).rightDerivedFunctor ≅ F.rightDerivedFunctor ⋙ G.rightDerivedFunctor` for exact
functors between abelian categories with K-injective resolutions, obtained from
`mapDerivedCategoryCompIso` by transport along the compatibility isomorphisms.

This does not assume `F.PreservesKInjectiveComplexes`, unlike
`Functor.rightDerivedFunctorCompIso` of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, which in turn
assumes `F.PreservesKInjectiveComplexes` instead of exactness. -/
noncomputable def rightDerivedFunctorCompIsoOfExact (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).rightDerivedFunctor ≅ F.rightDerivedFunctor ⋙ G.rightDerivedFunctor :=
  (F ⋙ G).rightDerivedFunctorIsoMapDerivedCategory ≪≫ (mapDerivedCategoryCompIso F G).symm ≪≫
    isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.symm G.mapDerivedCategory ≪≫
    isoWhiskerLeft F.rightDerivedFunctor G.rightDerivedFunctorIsoMapDerivedCategory.symm

/-- If `G` is exact, then `RF ⋙ RG`, equipped with the composite unit, is a right derived
functor of `(F ⋙ G).mapHomotopyCategory ⋙ Qh` for an arbitrary additive `F`: the unit of `RG`
is an isomorphism everywhere, so the composite unit is an isomorphism on K-injective
complexes. -/
lemma isRightDerivedFunctor_rightDerivedFunctor_comp_of_exact (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor
      (rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  change IsIso ((rightDerivedFunctorCompUnit F G).app
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
  have h₁ : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) := inferInstance
  dsimp [rightDerivedFunctorCompUnit]
  infer_instance

/-- The composition isomorphism `R(F ⋙ G) ≅ RF ⋙ G` for an arbitrary additive functor `F` and
an *exact* functor `G`, where `G` acts on derived categories levelwise. Unlike
`Functor.rightDerivedFunctorCompIso`, no K-injectivity condition on `F` is needed.

```
D(C) --R(F ⋙ G)--> D(E)
  |                ^
 RF                |
  v                |
D(D) ------G-------'
```
-/
noncomputable def rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived (F : C ⥤ D)
    (G : D ⥤ E) [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).rightDerivedFunctor ≅ F.rightDerivedFunctor ⋙ G.mapDerivedCategory :=
  have := isRightDerivedFunctor_rightDerivedFunctor_comp_of_exact F G
  rightDerivedUnique (F ⋙ G).rightDerivedFunctor
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
      (F ⋙ G).rightDerivedFunctorUnit (rightDerivedFunctorCompUnit F G)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ≪≫
    isoWhiskerLeft F.rightDerivedFunctor G.rightDerivedFunctorIsoMapDerivedCategory

end Composition

section CompositionExactRight

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [HasKInjectiveResolutions C]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The unit exhibiting `RF ⋙ D(G)` as a candidate right derived functor of
`(F ⋙ G).mapHomotopyCategory ⋙ Qh`, for an exact functor `G`: it is assembled from the unit
of `RF`, the comparison `G.mapDerivedCategoryFactorsh` and the composition isomorphism of
`mapHomotopyCategory`. -/
noncomputable def rightDerivedFunctorCompMapDerivedCategoryUnit :
    (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (F.rightDerivedFunctor ⋙ G.mapDerivedCategory) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactorsh.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.rightDerivedFunctorUnit G.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- If `G` is exact, then `RF ⋙ D(G)`, equipped with the unit
`rightDerivedFunctorCompMapDerivedCategoryUnit`, is a right derived functor of
`(F ⋙ G).mapHomotopyCategory ⋙ Qh`: by the K-injective right derivability structure it
suffices that the unit is an isomorphism on K-injective complexes, which holds since the unit
of `RF` is, and `D(G)` is computed levelwise. -/
instance isRightDerivedFunctor_rightDerivedFunctor_comp_mapDerivedCategory :
    (F.rightDerivedFunctor ⋙ G.mapDerivedCategory).IsRightDerivedFunctor
      (rightDerivedFunctorCompMapDerivedCategoryUnit F G)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  change IsIso ((rightDerivedFunctorCompMapDerivedCategoryUnit F G).app
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
  have h₁ : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) := inferInstance
  dsimp [rightDerivedFunctorCompMapDerivedCategoryUnit]
  infer_instance

/-- **Composition with an exact functor**: for an additive functor `F : C ⥤ D` and an *exact*
functor `G : D ⥤ E` between abelian categories, `R(F ⋙ G) ≅ RF ⋙ D(G)`: the right derived
functor of the composite is computed by applying `G` levelwise to `RF`. In contrast with
`Functor.rightDerivedFunctorCompIso`, no hypothesis on `F` is needed. -/
noncomputable def rightDerivedFunctorCompMapDerivedCategoryIso :
    (F ⋙ G).rightDerivedFunctor ≅ F.rightDerivedFunctor ⋙ G.mapDerivedCategory :=
  rightDerivedUnique (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.mapDerivedCategory)
    (F ⋙ G).rightDerivedFunctorUnit (rightDerivedFunctorCompMapDerivedCategoryUnit F G)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end CompositionExactRight

end CategoryTheory.Functor
