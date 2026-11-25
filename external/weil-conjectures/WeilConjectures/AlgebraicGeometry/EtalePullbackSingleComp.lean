/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-! # Pullback composition on a sheaf in degree zero

Source: Stacks Tag 0D6D, composition of derived pullback; Tag 09Z1, restriction maps.
(blueprint: lem-sbc-pullback-single-comp)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

set_option linter.flexible false in
private lemma single_hom (G : C ⥤ D) [G.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G] (n : ℤ) (X : C) :
    (G.mapDerivedCategorySingleFunctor n).hom.app X =
      G.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C (.up ℤ) n).obj X) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app X) := by
  simp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
  erw [Category.id_comp]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private lemma complex_single_comp (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
    (n : ℤ) (X : C) :
    (H.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app X) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) n).hom.app (G.obj X) =
    (HomologicalComplex.singleMapHomologicalComplex (G ⋙ H) (.up ℤ) n).hom.app X := by
  ext i
  by_cases hi : i = n
  · subst i
    simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

private lemma derived_single_comp (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H] (n : ℤ) (X : C) :
    (mapDerivedCategoryCompIso G H).inv.app ((DerivedCategory.singleFunctor C n).obj X) ≫
      H.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor n).hom.app X) ≫
      (H.mapDerivedCategorySingleFunctor n).hom.app (G.obj X) =
    ((G ⋙ H).mapDerivedCategorySingleFunctor n).hom.app X := by
  rw [single_hom G, single_hom H, single_hom (G ⋙ H), Functor.map_comp]
  simp only [Category.assoc]
  erw [mapDerivedCategoryFactors_hom_naturality_assoc]
  have hf := mapDerivedCategoryCompIso_fac G H
    ((HomologicalComplex.single C (.up ℤ) n).obj X)
  have hc : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).hom.app
      ((HomologicalComplex.single C (.up ℤ) n).obj X) = 𝟙 _ := rfl
  rw [hc] at hf
  erw [Functor.map_id, Category.comp_id] at hf
  erw [← DerivedCategory.Q.map_comp, complex_single_comp]
  erw [reassoc_of% hf]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
private lemma complex_single_natIso {G H : C ⥤ D} [G.Additive] [H.Additive]
    (e : G ≅ H) (n : ℤ) (X : C) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) n).obj X) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) n).hom.app X =
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app X ≫
      (HomologicalComplex.single D (.up ℤ) n).map (e.hom.app X) := by
  ext i
  by_cases hi : i = n
  · subst i
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      HomologicalComplex.single_map_f_self]
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, hi]

private lemma derived_single_natIso {G H : C ⥤ D} [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ≅ H) (n : ℤ) (X : C) :
    (mapDerivedCategoryNatIso e).hom.app ((DerivedCategory.singleFunctor C n).obj X) ≫
      (H.mapDerivedCategorySingleFunctor n).hom.app X =
    (G.mapDerivedCategorySingleFunctor n).hom.app X ≫
      (DerivedCategory.singleFunctor D n).map (e.hom.app X) := by
  rw [single_hom H, single_hom G]
  simp only [Category.assoc]
  erw [mapDerivedCategoryNatIso_fac_assoc, ← DerivedCategory.Q.map_comp,
    complex_single_natIso, DerivedCategory.Q.map_comp]
  rfl

private lemma plus_single_comp (G : C ⥤ D) (H : D ⥤ E) [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H] (n : ℤ) (X : C) :
    (mapDerivedCategoryPlusCompIso G H).hom.app
        ((DerivedCategory.Plus.singleFunctor C n).obj X) ≫
      H.mapDerivedCategoryPlus.map ((G.mapDerivedCategoryPlusSingleFunctor n).hom.app X) ≫
      (H.mapDerivedCategoryPlusSingleFunctor n).hom.app (G.obj X) =
    ((G ⋙ H).mapDerivedCategoryPlusSingleFunctor n).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  have hmap : ∀ {X Y : DerivedCategory.Plus D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (H.mapDerivedCategoryPlus.map f) =
        H.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := fun _ => rfl
  simp only [Functor.map_comp, hmap, ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  exact derived_single_comp G H n X

private lemma plus_single_natIso {G H : C ⥤ D} [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ≅ H) (n : ℤ) (X : C) :
    (mapDerivedCategoryPlusNatIso e).hom.app
        ((DerivedCategory.Plus.singleFunctor C n).obj X) ≫
      (H.mapDerivedCategoryPlusSingleFunctor n).hom.app X =
    (G.mapDerivedCategoryPlusSingleFunctor n).hom.app X ≫
      (DerivedCategory.Plus.singleFunctor D n).map (e.hom.app X) := by
  apply DerivedCategory.Plus.ι.map_injective
  have hsingle : ∀ {X Y : D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor D n).map f) =
        (DerivedCategory.singleFunctor D n).map f := fun _ => rfl
  simp only [Functor.map_comp, hsingle, ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  exact derived_single_natIso e n X

end CategoryTheory.Functor

namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Composition of the degree-zero comparisons for two exact étale pullbacks.

Source: Stacks Tags 0D6D and 09Z1; the coefficient identity in the proof of
lem-sbc-pullback-comparison-comp, step 2.
(blueprint: lem-sbc-pullback-single-comp)

Proof: represent F[0] by the single cochain complex on F. The composition comparison
for the levelwise pullbacks is the underived pullback composition comparison in degree
zero; in every other degree its components are the unique maps of zero objects. The
single-complex comparison for each pullback is the identity at degree zero, and the
canonical zero-object comparison elsewhere. Hence the two routes agree degreewise.
Apply the derived localization Q to these equalities. Expand the single-functor
comparison as the factorization comparison followed by Q of the levelwise single
comparison. Naturality of the factorization comparison and the factorization laws
for derived composition and derived natural isomorphisms identify the two routes.
The bounded-below comparisons are restrictions of these same isomorphisms along the
fully faithful inclusion D⁺ → D, which reflects equality. The inverse underived
composition comparison at the end gives exactly the displayed orientation. This
argument applies to identity morphisms and zero sheaves without extra assumptions.
-/
theorem Etale.upperStarPlusComp_single
    {T T₁ T₂ : Scheme.{u}} (π₁ : T₁ ⟶ T₂) (π₂ : T₂ ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    D+((π₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      ((((π₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl).inv.app F) =
    (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) π₁ π₂).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      ((((π₁ ≫ π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) :=
  by
    rw [← cancel_epi ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) π₁ π₂).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [Etale.upperStarPlusComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [reassoc_of% (Functor.plus_single_comp
      (π₂)^*[ModuleCat.{u + 1} Λ] (π₁)^*[ModuleCat.{u + 1} Λ] 0 F),
      reassoc_of% (Functor.plus_single_natIso
        (Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl) 0 F)]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry
