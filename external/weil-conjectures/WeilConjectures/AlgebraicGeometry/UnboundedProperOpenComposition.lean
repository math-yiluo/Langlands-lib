/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorAcyclic
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

/-!
# Unbounded proper/open composition

Source: Stacks Project, Tags 0F7C and 0F7D.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private lemma comp_fac
    {C D E : Type v} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) :
    Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso' F G e).hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh ≫
      H.rightDerivedFunctorUnit := by
  have hc : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso C (.up ℤ)) _

set_option backward.isDefEq.respectTransparency false in
private lemma comp_unit_app
    {C D E : Type v} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (T : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app T =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) := by
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi]
  erw [DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

-- Comparing iterated sheaf functors requires unfolding the derived-category interfaces.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
private lemma derived_comp_eq (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g f).hom =
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (ModuleCat.{u + 1} Λ) g) (lowerStar (ModuleCat.{u + 1} Λ) f)
        (lowerStarComp (ModuleCat.{u + 1} Λ) g f)).hom := by
  rw [Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (g ≫ f))
    _ (upperStarComp (ModuleCat.{u + 1} Λ) g f) (by
      exact (congrArg Iso.hom
        (conjugateIsoEquiv_upperStarComp (ModuleCat.{u + 1} Λ) g f)).symm)]
  simp only [rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv]
  rfl

private theorem geometric_comp_fac
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.rightDerivedFunctorCompUnit (f)_*[ModuleCat.{u + 1} Λ]
        (g)_*[ModuleCat.{u + 1} Λ] ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) f g).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory
          (lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom (.up ℤ)) DerivedCategory.Qh ≫
      ((f ≫ g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorUnit := by
  rw [derived_comp_eq Λ g f]
  exact comp_fac _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem generic_vertical_pasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type v}
    [Category.{w} A₀] [Category.{w} A₁] [Category.{w} A₂]
    [Category.{w} B₀] [Category.{w} B₁] [Category.{w} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
    [Abelian.HasKInjectiveResolutions A₀] [Abelian.HasKInjectiveResolutions A₁]
    [Abelian.HasKInjectiveResolutions B₀] [Abelian.HasKInjectiveResolutions B₁]
    (G₁ : A₀ ⥤ A₁) (G₂ : A₁ ⥤ A₂) (G : A₀ ⥤ A₂)
    (H₁ : B₀ ⥤ B₁) (H₂ : B₁ ⥤ B₂) (H : B₀ ⥤ B₂)
    (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (E₂ : A₂ ⥤ B₂)
    [G₁.Additive] [G₂.Additive] [G.Additive]
    [H₁.Additive] [H₂.Additive] [H.Additive]
    [E₀.Additive] [E₁.Additive] [E₂.Additive]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
    [G₁.PreservesKInjectiveComplexes] [H₁.PreservesKInjectiveComplexes]
    (g : G₁ ⋙ G₂ ≅ G) (h : H₁ ⋙ H₂ ≅ H)
    (e₁ : G₁ ⋙ E₁ ⟶ E₀ ⋙ H₁) (e₂ : G₂ ⋙ E₂ ⟶ E₁ ⋙ H₂)
    (e : G ⋙ E₂ ⟶ E₀ ⋙ H)
    (he : ∀ X, E₂.map (g.hom.app X) ≫ e.app X =
      e₂.app (G₁.obj X) ≫ H₂.map (e₁.app X) ≫ h.hom.app (E₀.obj X))
    (c₁ : G₁.rightDerivedFunctor ⋙ E₁.mapDerivedCategory ⟶
      E₀.mapDerivedCategory ⋙ H₁.rightDerivedFunctor)
    (c₂ : G₂.rightDerivedFunctor ⋙ E₂.mapDerivedCategory ⟶
      E₁.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (c : G.rightDerivedFunctor ⋙ E₂.mapDerivedCategory ⟶
      E₀.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hc₁ : ∀ J : HomotopyCategory A₀ (.up ℤ),
      E₁.mapDerivedCategory.map (G₁.rightDerivedFunctorUnit.app J) ≫
          c₁.app (DerivedCategory.Qh.obj J) =
        E₁.mapDerivedCategoryFactorsh.hom.app
          ((G₁.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app J) ≫
        H₁.rightDerivedFunctorUnit.app ((E₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H₁.rightDerivedFunctor.map (E₀.mapDerivedCategoryFactorsh.inv.app J))
    (hc₂ : ∀ J : HomotopyCategory A₁ (.up ℤ),
      E₂.mapDerivedCategory.map (G₂.rightDerivedFunctorUnit.app J) ≫
          c₂.app (DerivedCategory.Qh.obj J) =
        E₂.mapDerivedCategoryFactorsh.hom.app
          ((G₂.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₂ (.up ℤ)).app J) ≫
        H₂.rightDerivedFunctorUnit.app ((E₁.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H₂.rightDerivedFunctor.map (E₁.mapDerivedCategoryFactorsh.inv.app J))
    (hc : ∀ J : HomotopyCategory A₀ (.up ℤ),
      E₂.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app J) ≫
          c.app (DerivedCategory.Qh.obj J) =
        E₂.mapDerivedCategoryFactorsh.hom.app
          ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e (.up ℤ)).app J) ≫
        H.rightDerivedFunctorUnit.app ((E₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H.rightDerivedFunctor.map (E₀.mapDerivedCategoryFactorsh.inv.app J))
    (cG : G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor ≅ G.rightDerivedFunctor)
    (cH : H₁.rightDerivedFunctor ⋙ H₂.rightDerivedFunctor ≅ H.rightDerivedFunctor)
    (hcG : Functor.rightDerivedFunctorCompUnit G₁ G₂ ≫
        Functor.whiskerLeft DerivedCategory.Qh cG.hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory g.hom (.up ℤ))
        DerivedCategory.Qh ≫ G.rightDerivedFunctorUnit)
    (hcH : Functor.rightDerivedFunctorCompUnit H₁ H₂ ≫
        Functor.whiskerLeft DerivedCategory.Qh cH.hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory h.hom (.up ℤ))
        DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit)
    (K : DerivedCategory A₀) :
    c.app K =
      E₂.mapDerivedCategory.map
        (cG.inv.app K) ≫
      c₂.app (G₁.rightDerivedFunctor.obj K) ≫
      H₂.rightDerivedFunctor.map (c₁.app K) ≫
      cH.hom.app
        (E₀.mapDerivedCategory.obj K) := by
  let a : (G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor) ⋙
      E₂.mapDerivedCategory ⟶ E₀.mapDerivedCategory ⋙ H.rightDerivedFunctor :=
    Functor.whiskerRight cG.hom E₂.mapDerivedCategory ≫
      c
  let b : (G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor) ⋙
      E₂.mapDerivedCategory ⟶ E₀.mapDerivedCategory ⋙ H.rightDerivedFunctor :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft G₁.rightDerivedFunctor
        (c₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (c₁)
        H₂.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E₀.mapDerivedCategory cH.hom
  have hi (X : HomotopyCategory.KInjectives A₀) :
      IsIso ((Functor.rightDerivedFunctorCompUnit G₁ G₂).app
        ((HomotopyCategory.KInjectives.ι (C := A₀)).obj X)) := by
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    have h₁ : IsIso (G₁.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A₀ (.up ℤ)).obj J)) := inferInstance
    have h₂ : IsIso (G₂.rightDerivedFunctorUnit.app
      ((G₁.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A₀ (.up ℤ)).obj J))) := by
      change IsIso (G₂.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient A₁ (.up ℤ)).obj
          ((G₁.mapHomologicalComplex (.up ℤ)).obj J)))
      infer_instance
    let h₁ := h₁
    let h₂ := h₂
    change IsIso ((Functor.rightDerivedFunctorCompUnit G₁ G₂).app
      ((HomotopyCategory.quotient A₀ (.up ℤ)).obj J))
    rw [comp_unit_app G₁ G₂]
    exact (asIso (G₂.rightDerivedFunctorUnit.app _ ) ≪≫
      G₂.rightDerivedFunctor.mapIso (asIso (G₁.rightDerivedFunctorUnit.app _))).isIso_hom
  have : ((G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor) ⋙
      E₂.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight (Functor.rightDerivedFunctorCompUnit G₁ G₂)
        E₂.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A₀ (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (((G₁ ⋙ G₂).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        E₂.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun X ↦ ?_)
    let _ := hi X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    change IsIso (E₂.mapDerivedCategory.map
      ((Functor.rightDerivedFunctorCompUnit G₁ G₂).app
        ((HomotopyCategory.KInjectives.ι (C := A₀)).obj X)) ≫ 𝟙 _)
    infer_instance
  have hab : a = b := by
    apply Functor.rightDerived_ext
      ((G₁.rightDerivedFunctor ⋙ G₂.rightDerivedFunctor) ⋙ E₂.mapDerivedCategory)
      (Functor.whiskerRight (Functor.rightDerivedFunctorCompUnit G₁ G₂)
        E₂.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso A₀ (.up ℤ))
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Category.assoc]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
      Category.id_comp]
    have hcG := congr_app hcG J
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hcG
    erw [← E₂.mapDerivedCategory.map_comp_assoc, hcG,
      E₂.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    erw [hc J]
    have hn₂ := (c₂).naturality
      (G₁.rightDerivedFunctorUnit.app J)
    simp only [Functor.comp_map] at hn₂
    erw [comp_unit_app G₁ G₂ J, E₂.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    erw [reassoc_of% hn₂]
    erw [reassoc_of% hc₂ ((G₁.mapHomotopyCategory (.up ℤ)).obj J)]
    have h₁ := hc₁ J
    have h₁' : E₁.mapDerivedCategoryFactorsh.inv.app
        ((G₁.mapHomotopyCategory (.up ℤ)).obj J) ≫
        E₁.mapDerivedCategory.map (G₁.rightDerivedFunctorUnit.app J) ≫
        (c₁).app
          (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app J) ≫
        H₁.rightDerivedFunctorUnit.app ((E₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H₁.rightDerivedFunctor.map (E₀.mapDerivedCategoryFactorsh.inv.app J) := by
      apply (cancel_epi (E₁.mapDerivedCategoryFactorsh.hom.app
        ((G₁.mapHomotopyCategory (.up ℤ)).obj J))).1
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      simpa only [Functor.comp_obj, Category.assoc] using h₁
    erw [← H₂.rightDerivedFunctor.map_comp_assoc,
      ← H₂.rightDerivedFunctor.map_comp_assoc]
    simp only [Category.assoc]
    erw [h₁']
    erw [H₂.rightDerivedFunctor.map_comp, H₂.rightDerivedFunctor.map_comp]
    simp only [Category.assoc]
    have hn := H₂.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app J)
    simp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hnH := cH.hom.naturality (E₀.mapDerivedCategoryFactorsh.inv.app J)
    simp only [Functor.comp_map] at hnH
    erw [hnH]
    have hcH := congr_app hcH
      ((E₀.mapHomotopyCategory (.up ℤ)).obj J)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, comp_unit_app] at hcH
    erw [Category.assoc] at hcH
    erw [reassoc_of% hcH]
    have hnE := E₂.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory g.hom (.up ℤ)).app J)
    simp only [Functor.comp_map] at hnE
    simp only [Functor.comp_obj] at hnE
    erw [reassoc_of% hnE]
    have ht : Functor.whiskerRight g.hom E₂ ≫ e =
        Functor.whiskerLeft G₁ e₂ ≫ Functor.whiskerRight e₁ H₂ ≫
          Functor.whiskerLeft E₀ h.hom := by
      ext X
      exact he X
    have hh := congr_app
      (congrArg (fun t => NatTrans.mapHomotopyCategory t (.up ℤ)) ht) J
    simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
    change (E₂.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory g.hom (.up ℤ)).app J) ≫
          (NatTrans.mapHomotopyCategory e (.up ℤ)).app J =
      (NatTrans.mapHomotopyCategory e₂ (.up ℤ)).app
          ((G₁.mapHomotopyCategory (.up ℤ)).obj J) ≫
        (H₂.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app J) ≫
        (NatTrans.mapHomotopyCategory h.hom (.up ℤ)).app
          ((E₀.mapHomotopyCategory (.up ℤ)).obj J) at hh
    erw [← DerivedCategory.Qh.map_comp_assoc, hh]
    simp only [DerivedCategory.Qh.map_comp, Category.assoc]
    rfl
  apply (Iso.eq_inv_comp (E₂.mapDerivedCategory.mapIso (cG.app K))).2
  simpa only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.assoc,
    Category.id_comp, CategoryTheory.Functor.mapIso_hom, Iso.app_hom,
    Functor.comp_obj] using congr_app hab K

private theorem open_compare_mono
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (k : X ⟶ Y) [IsOpenImmersion k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) := by
  obtain ⟨L, ι, hi, _, ho, _⟩ := properSupportSheafComposition Λ
  have hι : Mono ((ι k).app F) := by
    refine ⟨fun {Z} a b hab ↦ ?_⟩
    ext V s
    apply (hi X Y k F V.unop).1
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun z ↦ z.hom) hab) V) s
  obtain ⟨o, he⟩ := ho X Y k
  have he' := congr_app he F
  dsimp only [NatTrans.comp_app] at he'
  rw [← he']
  infer_instance

private theorem ordinary_vertical (Λ : Type (u + 1)) [CommRing Λ]
    {A B C D E F : Scheme.{u}}
    (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
    (δ₁ : (r₁)_*[ModuleCat.{u + 1} Λ] ⋙ (i)_!open[ModuleCat.{u + 1} Λ] ≅
      (k)_!open[ModuleCat.{u + 1} Λ] ⋙ (p₁)_*[ModuleCat.{u + 1} Λ])
    (δ₂ : (r₂)_*[ModuleCat.{u + 1} Λ] ⋙ (j)_!open[ModuleCat.{u + 1} Λ] ≅
      (i)_!open[ModuleCat.{u + 1} Λ] ⋙ (p₂)_*[ModuleCat.{u + 1} Λ])
    (δ : (r₁ ≫ r₂)_*[ModuleCat.{u + 1} Λ] ⋙ (j)_!open[ModuleCat.{u + 1} Λ] ≅
      (k)_!open[ModuleCat.{u + 1} Λ] ⋙ (p₁ ≫ p₂)_*[ModuleCat.{u + 1} Λ])
    (hδ₁ : ∀ (X : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      δ₁.hom.app X ≫ (p₁)_*[ModuleCat.{u + 1} Λ].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k (p₁)).hom.app X =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app
        ((r₁)_*[ModuleCat.{u + 1} Λ].obj X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (r₁) i (k ≫ (p₁)) h₁).hom.app X)
    (hδ₂ : ∀ (X : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      δ₂.hom.app X ≫ (p₂)_*[ModuleCat.{u + 1} Λ].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) i (p₂)).hom.app X =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app
        ((r₂)_*[ModuleCat.{u + 1} Λ].obj X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (r₂) j (i ≫ (p₂)) h₂).hom.app X)
    (hδ : ∀ (X : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      δ.hom.app X ≫ (p₁ ≫ p₂)_*[ModuleCat.{u + 1} Λ].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k (p₁ ≫ p₂)).hom.app X =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app
        ((r₁ ≫ r₂)_*[ModuleCat.{u + 1} Λ].obj X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (r₁ ≫ r₂) j (k ≫ (p₁ ≫ p₂)) h).hom.app X)
    (X : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).map ((lowerStarComp (ModuleCat.{u + 1} Λ)
      r₁ r₂).hom.app X) ≫
        δ.hom.app X =
      δ₂.hom.app ((lowerStar (ModuleCat.{u + 1} Λ) r₁).obj X) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p₂).map (δ₁.hom.app X) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).hom.app ((openImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) k).obj X) := by
  have := open_compare_mono Λ k X
  apply (cancel_mono ((lowerStar (ModuleCat.{u + 1} Λ) (p₁ ≫ p₂)).map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X) ≫
    (lowerStarComp (ModuleCat.{u + 1} Λ) k (p₁ ≫ p₂)).hom.app X)).1
  simp only [Category.assoc]
  rw [hδ]
  have nc := (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂).hom.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app X)
  simp only [Functor.comp_map] at nc
  rw [← reassoc_of% nc]
  have hk := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) k p₁ p₂ (k ≫ p₁) (p₁ ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) rfl rfl (Category.assoc k p₁ p₂).symm) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hk
  rw [← hk, ← (lowerStar (ModuleCat.{u + 1} Λ) p₂).map_comp_assoc, ← (lowerStar (ModuleCat.{u + 1}
    Λ) p₂).map_comp_assoc]
  simp only [Category.assoc]
  rw [hδ₁]
  rw [(lowerStar (ModuleCat.{u + 1} Λ) p₂).map_comp]
  simp only [Category.assoc]
  have hi := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) r₁ i p₂ (k ≫ p₁) (i ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) h₁ rfl (Category.assoc k p₁ p₂).symm) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hi
  rw [hi, reassoc_of% hδ₂ ((lowerStar (ModuleCat.{u + 1} Λ) r₁).obj X)]
  have nj := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).naturality
    ((lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂).hom.app X)
  rw [reassoc_of% nj]
  have hr := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) r₁ r₂ j (r₁ ≫ r₂) (i ≫ p₂)
    (k ≫ (p₁ ≫ p₂)) rfl h₂ h) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hr
  rw [hr]

end AlgebraicGeometry.Etale
