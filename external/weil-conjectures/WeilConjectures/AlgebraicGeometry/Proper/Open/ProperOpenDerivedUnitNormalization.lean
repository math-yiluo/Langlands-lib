/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality

/-! # The derived adjunction-unit equation for a normalized open triangle

## References

* Stacks Project, More on Etale Cohomology, Tag 0F7B, specialized to a triangle fixing the open
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem homotopy_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {J : C ⥤ D} {U : D ⥤ C} [J.Additive] [U.Additive] (a : J ⊣ U)
    (K : HomotopyCategory.Plus C) :
    a.mapHomotopyCategoryPlus.unit.app K =
      (NatTrans.mapHomotopyCategoryPlus a.unit).app K := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  have h (Z : HomotopyCategory C (ComplexShape.up ℤ)) :
      (a.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app Z =
        (NatTrans.mapHomotopyCategory a.unit (ComplexShape.up ℤ)).app Z := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    rfl
  exact h K.obj

private theorem homotopy_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {J : C ⥤ D} {U : D ⥤ C} [J.Additive] [U.Additive] (a : J ⊣ U)
    (K : HomotopyCategory.Plus D) :
    a.mapHomotopyCategoryPlus.counit.app K =
      (NatTrans.mapHomotopyCategoryPlus a.counit).app K := by
  apply (HomotopyCategory.Plus.ι D).map_injective
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_counit_app,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  have h (Z : HomotopyCategory D (ComplexShape.up ℤ)) :
      (a.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app Z =
        (NatTrans.mapHomotopyCategory a.counit (ComplexShape.up ℤ)).app Z := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    rfl
  exact h K.obj

private theorem homotopy_whisker_right
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    (H : D ⥤ E) [H.Additive] (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight α H)).app K =
      H.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus α).app K) := rfl

private theorem homotopy_whisker_left
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) [F.Additive] {G H : D ⥤ E} [G.Additive] [H.Additive]
    (α : G ⟶ H) (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft F α)).app K =
      (NatTrans.mapHomotopyCategoryPlus α).app (F.mapHomotopyCategoryPlus.obj K) := rfl

private theorem ordinary_unit
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (F : Sheaf X.smallEtaleTopology A)
    (g : (openImmersionLowerShriek A j₂).obj F ⟶
      (lowerStar A p).obj ((openImmersionLowerShriek A j₁).obj F))
    (hg : g ≫ (lowerStar A p).map
        ((openImmersionLowerShriekToLowerStar A j₁).app F) ≫
        (lowerStarComp A j₁ p j₂ h.symm).hom.app F =
      (openImmersionLowerShriekToLowerStar A j₂).app F) :
    (openImmersionLowerShriekUpperStarAdjunction A j₂).unit.app F ≫
      (upperStar A j₂).map g ≫
      (upperStarComp A j₁ p j₂ h.symm).hom.app _ ≫
      (upperStar A j₁).map ((upperStarLowerStarAdjunction A p).counit.app _) =
    (openImmersionLowerShriekUpperStarAdjunction A j₁).unit.app F := by
  have hi : IsIso ((upperStar A j₁).map
      ((openImmersionLowerShriekToLowerStar A j₁).app F) ≫
        (upperStarLowerStarAdjunction A j₁).counit.app F) := by
    rw [← IsIso.inv_eq_of_hom_inv_id
      (unit_map_openImmersionLowerShriekToLowerStar_app_counit A j₁ F)]
    infer_instance
  apply (cancel_mono ((upperStar A j₁).map
    ((openImmersionLowerShriekToLowerStar A j₁).app F) ≫
      (upperStarLowerStarAdjunction A j₁).counit.app F)).mp
  simp only [Category.assoc]
  rw [unit_map_openImmersionLowerShriekToLowerStar_app_counit]
  have hc :
      (upperStarComp A j₁ p j₂ h.symm).hom.app
          ((lowerStar A p).obj ((lowerStar A j₁).obj F)) ≫
        (upperStar A j₁).map ((upperStarLowerStarAdjunction A p).counit.app
          ((lowerStar A j₁).obj F)) ≫
        (upperStarLowerStarAdjunction A j₁).counit.app F =
      (upperStar A j₂).map ((lowerStarComp A j₁ p j₂ h.symm).hom.app F) ≫
        (upperStarLowerStarAdjunction A j₂).counit.app F := by
    have hconj : conjugateEquiv
        ((upperStarLowerStarAdjunction A p).comp (upperStarLowerStarAdjunction A j₁))
        (upperStarLowerStarAdjunction A j₂)
        (upperStarComp A j₁ p j₂ h.symm).hom =
        (lowerStarComp A j₁ p j₂ h.symm).hom :=
      congrArg Iso.hom (conjugateIsoEquiv_upperStarComp A j₁ p j₂ h.symm)
    have hc := conjugateEquiv_counit
      ((upperStarLowerStarAdjunction A p).comp (upperStarLowerStarAdjunction A j₁))
      (upperStarLowerStarAdjunction A j₂) (upperStarComp A j₁ p j₂ h.symm).hom F
    rw [hconj] at hc
    simpa only [Adjunction.comp_counit_app, Functor.comp_obj, Category.assoc] using hc.symm
  have hn := (upperStarLowerStarAdjunction A p).counit.naturality
    ((openImmersionLowerShriekToLowerStar A j₁).app F)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, ← hn, Functor.map_comp, Category.assoc]
  have hs := (upperStarComp A j₁ p j₂ h.symm).hom.naturality
    ((lowerStar A p).map ((openImmersionLowerShriekToLowerStar A j₁).app F))
  simp only [Functor.comp_obj, Functor.comp_map] at hs
  rw [← reassoc_of% hs]
  rw [hc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hg,
    unit_map_openImmersionLowerShriekToLowerStar_app_counit]

private theorem localized_triangle
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives D]
    (J₁ : C ⥤ D) (U₁ : D ⥤ C) (J₂ : C ⥤ E) (U₂ : E ⥤ C)
    (L : E ⥤ D) (R : D ⥤ E)
    [J₁.Additive] [U₁.Additive] [J₂.Additive] [U₂.Additive]
    [L.Additive] [R.Additive]
    [PreservesFiniteLimits J₁] [PreservesFiniteColimits J₁]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits J₂] [PreservesFiniteColimits J₂]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R)
    (ν₁ : 𝟭 C ⟶ J₁ ⋙ U₁) (ν₂ : 𝟭 C ⟶ J₂ ⋙ U₂)
    (η₁ : 𝟭 (DerivedCategory.Plus C) ⟶ J₁.mapDerivedCategoryPlus ⋙ U₁.mapDerivedCategoryPlus)
    (η₂ : 𝟭 (DerivedCategory.Plus C) ⟶ J₂.mapDerivedCategoryPlus ⋙ U₂.mapDerivedCategoryPlus)
    (ha : ∀ K, η₁.app (DerivedCategory.Plus.Qh.obj K) ≫
      U₁.mapDerivedCategoryPlus.map (J₁.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      U₁.mapDerivedCategoryPlusFactorsh.hom.app (J₁.mapHomotopyCategoryPlus.obj K) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus ν₁).app K))
    (hb : ∀ K, η₂.app (DerivedCategory.Plus.Qh.obj K) ≫
      U₂.mapDerivedCategoryPlus.map (J₂.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      U₂.mapDerivedCategoryPlusFactorsh.hom.app (J₂.mapHomotopyCategoryPlus.obj K) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus ν₂).app K))
    (g : J₂ ⟶ J₁ ⋙ R) (σ : U₂ ⟶ L ⋙ U₁)
    (d : J₂.mapDerivedCategoryPlus ⟶ J₁.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus)
    (s : U₂.mapDerivedCategoryPlus ⟶ L.mapDerivedCategoryPlus ⋙ U₁.mapDerivedCategoryPlus)
    (hd : ∀ K, d.app (DerivedCategory.Plus.Qh.obj K) ≫
      R.rightDerivedFunctorPlus.map (J₁.mapDerivedCategoryPlusFactorsh.hom.app K) =
        J₂.mapDerivedCategoryPlusFactorsh.hom.app K ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus g).app K) ≫
          R.rightDerivedFunctorPlusUnith.app (J₁.mapHomotopyCategoryPlus.obj K))
    (hs : ∀ K, s.app (DerivedCategory.Plus.Qh.obj K) ≫
      U₁.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      U₁.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
        U₂.mapDerivedCategoryPlusFactorsh.hom.app K ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ).app K))
    (hh : ∀ K, (NatTrans.mapHomotopyCategoryPlus ν₂).app K ≫
      U₂.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus g).app K) ≫
      (NatTrans.mapHomotopyCategoryPlus σ).app
        (R.mapHomotopyCategoryPlus.obj (J₁.mapHomotopyCategoryPlus.obj K)) ≫
      U₁.mapHomotopyCategoryPlus.map
        (a.mapHomotopyCategoryPlus.counit.app (J₁.mapHomotopyCategoryPlus.obj K)) =
      (NatTrans.mapHomotopyCategoryPlus ν₁).app K)
    (K : DerivedCategory.Plus C) :
    η₂.app K ≫ U₂.mapDerivedCategoryPlus.map (d.app K) ≫
      s.app (R.rightDerivedFunctorPlus.obj (J₁.mapDerivedCategoryPlus.obj K)) ≫
      U₁.mapDerivedCategoryPlus.map
        (a.derivedPlus.counit.app (J₁.mapDerivedCategoryPlus.obj K)) = η₁.app K := by
  let τ := η₂ ≫ Functor.whiskerRight d U₂.mapDerivedCategoryPlus ≫
    Functor.whiskerLeft (J₁.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus) s ≫
    Functor.whiskerLeft J₁.mapDerivedCategoryPlus
      (Functor.whiskerRight a.derivedPlus.counit U₁.mapDerivedCategoryPlus)
  have ht : τ = η₁ := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro N
    simp only [τ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj]
    apply (cancel_mono (U₁.mapDerivedCategoryPlus.map
      (J₁.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        U₁.mapDerivedCategoryPlusFactorsh.hom.app (J₁.mapHomotopyCategoryPlus.obj N))).mp
    simp only [Category.assoc]
    have hn := a.derivedPlus.counit.naturality (J₁.mapDerivedCategoryPlusFactorsh.hom.app N)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hn
    rw [← Functor.map_comp_assoc, ← hn, Functor.map_comp, Category.assoc]
    have sn := s.naturality
      (R.rightDerivedFunctorPlus.map (J₁.mapDerivedCategoryPlusFactorsh.hom.app N))
    simp only [Functor.comp_obj, Functor.comp_map] at sn
    rw [← reassoc_of% sn, ← Functor.map_comp_assoc, hd]
    simp only [Functor.map_comp, Category.assoc]
    have su := s.naturality
      (R.rightDerivedFunctorPlusUnith.app (J₁.mapHomotopyCategoryPlus.obj N))
    simp only [Functor.comp_obj, Functor.comp_map] at su
    rw [reassoc_of% su, ← U₁.mapDerivedCategoryPlus.map_comp_assoc,
      a.derivedPlus_counit_app_fac]
    simp only [Functor.map_comp, Category.assoc]
    have un := U₁.mapDerivedCategoryPlusFactorsh.hom.naturality
      (a.mapHomotopyCategoryPlus.counit.app (J₁.mapHomotopyCategoryPlus.obj N))
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at un
    erw [un]
    rw [reassoc_of% hs]
    have gn := U₂.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus g).app N)
    simp only [Functor.comp_obj, Functor.comp_map] at gn
    erw [reassoc_of% gn]
    rw [reassoc_of% hb, ha]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hh]
  exact NatTrans.congr_app ht K

private theorem normalized_lift_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    (G : C ⥤ C) (J₁ : C ⥤ D) (J₂ : C ⥤ E) (R : D ⥤ E)
    [G.Additive] [J₁.Additive] [J₂.Additive] [R.Additive]
    [PreservesFiniteLimits J₁] [PreservesFiniteColimits J₁]
    [PreservesFiniteLimits J₂] [PreservesFiniteColimits J₂]
    (e : G ≅ 𝟭 C) (i : G.rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus C))
    (hi : ∀ N : HomotopyCategory.Plus C,
      i.inv.app (DerivedCategory.Plus.Qh.obj N) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.inv).app N) ≫
          G.rightDerivedFunctorPlusUnith.app N)
    (δ : G ⋙ J₂ ⟶ J₁ ⋙ R) (N : HomotopyCategory.Plus C) :
    (J₂.mapDerivedCategoryPlus.map (i.inv.app (DerivedCategory.Plus.Qh.obj N)) ≫
      (Functor.rightDerivedFunctorPlusBaseChange δ).app (DerivedCategory.Plus.Qh.obj N)) ≫
      R.rightDerivedFunctorPlus.map (J₁.mapDerivedCategoryPlusFactorsh.hom.app N) =
    J₂.mapDerivedCategoryPlusFactorsh.hom.app N ≫
      DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight e.inv J₂ ≫ δ)).app N) ≫
      R.rightDerivedFunctorPlusUnith.app (J₁.mapHomotopyCategoryPlus.obj N) := by
  rw [Category.assoc, hi, Functor.map_comp]
  simp only [Category.assoc]
  rw [Functor.rightDerivedFunctorPlusBaseChange_fac_app_assoc,
    ← R.rightDerivedFunctorPlus.map_comp, Iso.inv_hom_id_app]
  erw [R.rightDerivedFunctorPlus.map_id]
  simp only [Category.comp_id]
  have hn := J₂.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategoryPlus e.inv).app N)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  erw [reassoc_of% hn]
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
    homotopy_whisker_right, Functor.map_comp, Category.assoc]
  have hf := J₂.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryPlusIdIso C).hom.app N)
  simp only [Functor.mapHomotopyCategoryPlusIdIso_hom_app_eq_id, Functor.comp_map,
    Functor.id_obj] at hf
  erw [DerivedCategory.Plus.Qh.map_id, J₂.mapDerivedCategoryPlus.map_id,
    J₂.mapHomotopyCategoryPlus.map_id, DerivedCategory.Plus.Qh.map_id] at hf
  erw [Category.id_comp, Category.comp_id] at hf
  erw [hf]

private theorem homotopy_triangle
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (J₁ : C ⥤ D) (U₁ : D ⥤ C) (J₂ : C ⥤ E) (U₂ : E ⥤ C)
    (L : E ⥤ D) (R : D ⥤ E)
    [J₁.Additive] [U₁.Additive] [J₂.Additive] [U₂.Additive]
    [L.Additive] [R.Additive]
    (a : L ⊣ R) (a₁ : J₁ ⊣ U₁) (a₂ : J₂ ⊣ U₂)
    (g : J₂ ⟶ J₁ ⋙ R) (σ : U₂ ⟶ L ⋙ U₁)
    (ho : ∀ F, a₂.unit.app F ≫ U₂.map (g.app F) ≫
      σ.app (R.obj (J₁.obj F)) ≫ U₁.map (a.counit.app (J₁.obj F)) = a₁.unit.app F)
    (N : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus a₂.unit).app N ≫
      U₂.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus g).app N) ≫
      (NatTrans.mapHomotopyCategoryPlus σ).app
        (R.mapHomotopyCategoryPlus.obj (J₁.mapHomotopyCategoryPlus.obj N)) ≫
      U₁.mapHomotopyCategoryPlus.map
        (a.mapHomotopyCategoryPlus.counit.app (J₁.mapHomotopyCategoryPlus.obj N)) =
      (NatTrans.mapHomotopyCategoryPlus a₁.unit).app N := by
  have hn : a₂.unit ≫ Functor.whiskerRight g U₂ ≫
      Functor.whiskerLeft (J₁ ⋙ R) σ ≫
      Functor.whiskerLeft J₁ (Functor.whiskerRight a.counit U₁) = a₁.unit := by
    exact NatTrans.ext (funext ho)
  have hh := NatTrans.congr_app (congrArg NatTrans.mapHomotopyCategoryPlus hn) N
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
    homotopy_whisker_right, homotopy_whisker_left] at hh
  rw [homotopy_counit]
  exact hh

private theorem ordinary_normalized
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] {T₁ T₂ X : Scheme.{u}}
    (p : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (δ : lowerStar A (𝟙 X) ⋙
        openImmersionLowerShriek A j₂ ⟶
      openImmersionLowerShriek A j₁ ⋙
        lowerStar A p)
    (hδ : ∀ F, δ.app F ≫ (lowerStar A p).map
          ((openImmersionLowerShriekToLowerStar A j₁).app F) ≫
          (lowerStarComp A j₁ p).hom.app F =
        (openImmersionLowerShriekToLowerStar A j₂).app
            ((lowerStar A (𝟙 X)).obj F) ≫
          (lowerStarComp A (𝟙 X) j₂ (j₁ ≫ p)
            (h.trans (Category.id_comp j₂).symm)).hom.app F)
    (F : Sheaf X.smallEtaleTopology A) :
    (openImmersionLowerShriek A j₂).map
        ((lowerStarId A X).inv.app F) ≫
      δ.app F ≫ (lowerStar A p).map
        ((openImmersionLowerShriekToLowerStar A j₁).app F) ≫
      (lowerStarComp A j₁ p j₂ h.symm).hom.app F =
    (openImmersionLowerShriekToLowerStar A j₂).app F := by
  subst j₂
  rw [hδ F, lowerStarComp_id_left]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  have hn := (openImmersionLowerShriekToLowerStar A
    (j₁ ≫ p)).naturality ((lowerStarId A X).inv.app F)
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(lowerStar A (j₁ ≫ p)).map_id F]
  simp only [Category.id_comp, Category.comp_id]

attribute [local irreducible] upperStarLowerStarAdjunction Adjunction.derivedPlus
  upperStarCompDerivedPlus

private theorem coefficient_unit_normalization
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] {T₁ T₂ X : Scheme.{u}}
    (p : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (δ : lowerStar A (𝟙 X) ⋙
        openImmersionLowerShriek A j₂ ⟶
      openImmersionLowerShriek A j₁ ⋙
        lowerStar A p)
    (hδ : ∀ F, δ.app F ≫ (lowerStar A p).map
          ((openImmersionLowerShriekToLowerStar A j₁).app F) ≫
          (lowerStarComp A j₁ p).hom.app F =
        (openImmersionLowerShriekToLowerStar A j₂).app
            ((lowerStar A (𝟙 X)).obj F) ≫
          (lowerStarComp A (𝟙 X) j₂ (j₁ ≫ p)
            (h.trans (Category.id_comp j₂).symm)).hom.app F)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        A j₂).unit.app K ≫
      (upperStar A j₂).mapDerivedCategoryPlus.map
        ((openImmersionLowerShriek A j₂).mapDerivedCategoryPlus.map
            ((lowerStarIdDerivedPlus A X).inv.app K) ≫
          (Functor.rightDerivedFunctorPlusBaseChange δ).app K) ≫
      (upperStarCompDerivedPlus A j₁ p j₂ h.symm).hom.app
        ((rightDerivedLowerStarPlus A p).obj
          ((openImmersionLowerShriek A j₁).mapDerivedCategoryPlus.obj K)) ≫
      (upperStar A j₁).mapDerivedCategoryPlus.map
        ((upperStarLowerStarAdjunction A p).derivedPlus.counit.app
          ((openImmersionLowerShriek A j₁).mapDerivedCategoryPlus.obj K)) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        A j₁).unit.app K := by
  let J₁ := openImmersionLowerShriek A j₁
  let J₂ := openImmersionLowerShriek A j₂
  let U₁ := upperStar A j₁
  let U₂ := upperStar A j₂
  let L := upperStar A p
  let R := lowerStar A p
  let a := upperStarLowerStarAdjunction A p
  let a₁ := openImmersionLowerShriekUpperStarAdjunction A j₁
  let a₂ := openImmersionLowerShriekUpperStarAdjunction A j₂
  let g : J₂ ⟶ J₁ ⋙ R :=
    Functor.whiskerRight (lowerStarId A X).inv J₂ ≫ δ
  let σ : U₂ ⟶ L ⋙ U₁ := (upperStarComp A j₁ p j₂ h.symm).hom
  let d : J₂.mapDerivedCategoryPlus ⟶ J₁.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus :=
    Functor.whiskerRight (lowerStarIdDerivedPlus A X).inv J₂.mapDerivedCategoryPlus ≫
      Functor.rightDerivedFunctorPlusBaseChange δ
  let s : U₂.mapDerivedCategoryPlus ⟶ L.mapDerivedCategoryPlus ⋙ U₁.mapDerivedCategoryPlus :=
    (upperStarCompDerivedPlus A j₁ p j₂ h.symm).hom
  have hg : ∀ F, g.app F ≫ R.map
      ((openImmersionLowerShriekToLowerStar A j₁).app F) ≫
      (lowerStarComp A j₁ p j₂ h.symm).hom.app F =
      (openImmersionLowerShriekToLowerStar A j₂).app F := by
    intro F
    simpa only [g, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc] using
      ordinary_normalized A p j₁ j₂ h δ hδ F
  have ho : ∀ F, a₂.unit.app F ≫ U₂.map (g.app F) ≫
      σ.app (R.obj (J₁.obj F)) ≫ U₁.map (a.counit.app (J₁.obj F)) = a₁.unit.app F := by
    intro F
    exact ordinary_unit A p j₁ j₂ h F (g.app F) (hg F)
  have hd (N : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A)) :
      d.app (DerivedCategory.Plus.Qh.obj N) ≫
        R.rightDerivedFunctorPlus.map (J₁.mapDerivedCategoryPlusFactorsh.hom.app N) =
      J₂.mapDerivedCategoryPlusFactorsh.hom.app N ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus g).app N) ≫
        R.rightDerivedFunctorPlusUnith.app (J₁.mapHomotopyCategoryPlus.obj N) := by
    exact normalized_lift_fac (lowerStar A (𝟙 X)) J₁ J₂ R (lowerStarId A X)
      (lowerStarIdDerivedPlus A X) (lowerStarIdDerivedPlus_inv_app A X) δ N
  apply localized_triangle J₁ U₁ J₂ U₂ L R a a₁.unit a₂.unit
    a₁.mapDerivedCategoryPlusAdjunction.unit a₂.mapDerivedCategoryPlusAdjunction.unit
    _ _ g σ d s hd _ _ K
  · intro N
    exact (a₁.mapDerivedCategoryPlusAdjunction_unit_app_fac N).trans
      (congrArg DerivedCategory.Plus.Qh.map (homotopy_unit a₁ N))
  · intro N
    exact (a₂.mapDerivedCategoryPlusAdjunction_unit_app_fac N).trans
      (congrArg DerivedCategory.Plus.Qh.map (homotopy_unit a₂ N))
  · exact upperStarCompDerivedPlus_hom_app_factorsh A j₁ p j₂ h.symm
  · exact homotopy_triangle J₁ U₁ J₂ U₂ L R a a₁ a₂ g σ ho

/-- A normalized ordinary open triangle satisfies the derived unit/counit equation.
No properness, finiteness, or invertibility of the ordinary transformation is required. -/
theorem properOpenDerivedUnitNormalization
    (Λ : Type (u + 1)) [CommRing Λ] {T₁ T₂ X : Scheme.{u}}
    (p : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂)
    (δ : lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂ ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁ ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p)
    (hδ : ∀ F, δ.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j₁).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) j₁ p).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j₂).app
            ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 X) j₂ (j₁ ≫ p)
            (h.trans (Category.id_comp j₂).symm)).hom.app F)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) j₂).unit.app K ≫
      (upperStar (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
            ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
          (Functor.rightDerivedFunctorPlusBaseChange δ).app K) ≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j₁ p j₂ h.symm).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)) ≫
      (upperStar (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).derivedPlus.counit.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) j₁).unit.app K := by
  exact coefficient_unit_normalization (ModuleCat.{u + 1} Λ) p j₁ j₂ h δ hδ K

end AlgebraicGeometry.Etale
