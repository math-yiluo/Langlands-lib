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
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Unbounded proper/open Pasting

Source: Stacks Project, Tags 0F7C and 0F7D.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem exact_identity_fac
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    (E : A ⥤ A) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (e : E ≅ 𝟭 A) (J : HomotopyCategory A (.up ℤ)) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Qh.obj J) =
      E.mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj, Functor.mapDerivedCategoryNatIso_fach]

/-- For an open immersion, extension by zero embeds into direct image.
Source: Stacks Project, More on Etale Cohomology, Tags 0F4X and 0F50:
the proper-support inclusion is sectionwise injective and identifies with this comparison
(auxiliary; not a blueprint node). -/
theorem mono_openImmersionLowerShriekToLowerStar_app
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

private theorem ordinary_identity_vertical
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}}
    (k : A ⟶ B) [IsOpenImmersion k]
    (δ : lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B))
    (hn : ∀ F, δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B)).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k (k ≫ 𝟙 B)
            ((Category.comp_id k).trans (Category.id_comp k).symm)).hom.app F)
    (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    δ.hom.app F ≫ (lowerStarId (ModuleCat.{u + 1} Λ) B).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj F) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
        ((lowerStarId (ModuleCat.{u + 1} Λ) A).hom.app F) := by
  have := mono_openImmersionLowerShriekToLowerStar_app Λ k F
  apply (cancel_mono
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F)).1
  have hnaux (f : A ⟶ B) (hf : f = k ≫ 𝟙 B) :
      δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B) f hf).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k f
            (hf.trans ((Category.comp_id k).trans (Category.id_comp k).symm))).hom.app F := by
    subst f
    exact hn F
  have hn' : δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B) k
            (Category.comp_id k).symm).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k k
            (Category.id_comp k).symm).hom.app F := by
    exact hnaux k (Category.comp_id k).symm
  rw [lowerStarComp_id_right, lowerStarComp_id_left] at hn'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at hn'
  erw [Category.comp_id, Category.comp_id] at hn'
  simp only [Category.assoc]
  have hid := (lowerStarId (ModuleCat.{u + 1} Λ) B).hom.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F)
  simp only [Functor.id_map] at hid
  rw [← hid, hn']
  exact ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).naturality
    ((lowerStarId (ModuleCat.{u + 1} Λ) A).hom.app F)).symm

private theorem open_identity_comparison
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).app F ≫
        (lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F =
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
        (upperStarId (ModuleCat.{u + 1} Λ) X)).hom.app F := by
  let adj := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)
  let e := upperStarId (ModuleCat.{u + 1} Λ) X
  let l := Adjunction.leftAdjointIdIso adj e
  apply (adj.homEquiv F F).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hl := unit_conjugateEquiv Adjunction.id adj l.hom F
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at hl
  have hl' : e.inv.app F = adj.unit.app F ≫
      (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)).map (l.hom.app F) := by
    change 𝟙 F ≫ e.inv.app F = _ at hl
    simpa only [Category.id_comp] using hl
  erw [← hl']
  have hh : (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)).map
        ((lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit.app F ≫
        e.inv.app F := by
    apply (cancel_mono (e.hom.app F)).1
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    have hn := e.hom.naturality ((lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F)
    simp only [Functor.id_map] at hn
    erw [hn, ← upperStarId_inv_app_counit_app, Iso.hom_inv_id_app_assoc]
  rw [CategoryTheory.Functor.map_comp]
  erw [hh]
  have hn := unit_map_openImmersionLowerShriekToLowerStar_app_counit
    (ModuleCat.{u + 1} Λ) (𝟙 X) F
  have hn' := congrArg (fun z ↦ z ≫ e.inv.app F) hn
  erw [Category.id_comp] at hn'
  simpa only [Category.assoc] using hn'

private theorem ordinary_identity_horizontal
    (Λ : Type (u + 1)) [CommRing Λ]
    {A C : Scheme.{u}} (r : A ⟶ C)
    (δ : lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 C) ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 A) ⋙
        lowerStar (ModuleCat.{u + 1} Λ) r)
    (hn : ∀ F, δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) r).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 C)).app
        ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r (𝟙 C) ((𝟙 A) ≫ r)
          ((Category.id_comp r).trans (Category.comp_id r).symm)).hom.app F)
    (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
        ((Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A))
          (upperStarId (ModuleCat.{u + 1} Λ) A)).hom.app F) =
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C))
        (upperStarId (ModuleCat.{u + 1} Λ) C)).hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) := by
  have hnaux (f : A ⟶ C) (hf : f = (𝟙 A) ≫ r) :
      δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) r f hf).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 C)).app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) r (𝟙 C) f
            (hf.trans ((Category.id_comp r).trans (Category.comp_id r).symm))).hom.app F := by
    subst f
    exact hn F
  have hn' := hnaux r (Category.id_comp r).symm
  rw [lowerStarComp_id_left, lowerStarComp_id_right] at hn'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app] at hn'
  erw [Category.comp_id, Category.comp_id] at hn'
  rw [← open_identity_comparison Λ A F,
    ← open_identity_comparison Λ C ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F),
    CategoryTheory.Functor.map_comp, ← Category.assoc]
  exact hn'

private theorem derived_vertical_identity
    {A B : Type v} [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (G : A ⥤ A) (H : B ⥤ B) (E : A ⥤ B)
    [G.Additive] [H.Additive] [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (eG : G ≅ 𝟭 A) (eH : H ≅ 𝟭 B) (δ : G ⋙ E ⟶ E ⋙ H)
    (γ : G.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      E.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hδ : ∀ F, δ.app F ≫ eH.hom.app (E.obj F) = E.map (eG.hom.app F))
    (hγ : ∀ J : HomotopyCategory A (.up ℤ),
      E.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app J) ≫
        γ.app (DerivedCategory.Qh.obj J) =
      E.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory δ (.up ℤ)).app J) ≫
        H.rightDerivedFunctorUnit.app ((E.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H.rightDerivedFunctor.map (E.mapDerivedCategoryFactorsh.inv.app J))
    (ia : G.rightDerivedFunctor ⟶ 𝟭 (DerivedCategory A))
    (ib : H.rightDerivedFunctor ≅ 𝟭 (DerivedCategory B))
    (ha : ∀ J, G.rightDerivedFunctorUnit.app J ≫
      ia.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory eG.hom (.up ℤ)).app J))
    (hb : ∀ J, H.rightDerivedFunctorUnit.app J ≫
      ib.hom.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory eH.hom (.up ℤ)).app J))
    (K : DerivedCategory A) :
    γ.app K = E.mapDerivedCategory.map (ia.app K) ≫
      ib.inv.app (E.mapDerivedCategory.obj K) := by
  let a : G.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      E.mapDerivedCategory := γ ≫ Functor.whiskerLeft E.mapDerivedCategory ib.hom
  let b : G.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      E.mapDerivedCategory := Functor.whiskerRight ia E.mapDerivedCategory
  have : (G.rightDerivedFunctor ⋙ E.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight G.rightDerivedFunctorUnit E.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
        E.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun X => ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    have hi : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj J)) := inferInstance
    change IsIso (E.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj J)) ≫ 𝟙 _)
    infer_instance
  have hab : a = b := by
    apply Functor.rightDerived_ext (G.rightDerivedFunctor ⋙ E.mapDerivedCategory)
      (Functor.whiskerRight G.rightDerivedFunctorUnit E.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.assoc]
    simp only [Functor.comp_obj]
    erw [Category.id_comp, Category.id_comp]
    erw [reassoc_of% hγ J]
    have hn := ib.hom.naturality (E.mapDerivedCategoryFactorsh.inv.app J)
    simp only [Functor.id_map] at hn
    erw [hn]
    erw [reassoc_of% hb ((E.mapHomotopyCategory (.up ℤ)).obj J)]
    have ht : δ ≫ Functor.whiskerLeft E eH.hom =
        Functor.whiskerRight eG.hom E := by
      ext F
      exact hδ F
    have hh := congr_app (congrArg (fun t => NatTrans.mapHomotopyCategory t (.up ℤ)) ht) J
    simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
    change (NatTrans.mapHomotopyCategory δ (.up ℤ)).app J ≫
        (NatTrans.mapHomotopyCategory eH.hom (.up ℤ)).app ((E.mapHomotopyCategory (.up ℤ)).obj J) =
      (E.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory eG.hom (.up ℤ)).app J) at hh
    erw [← DerivedCategory.Qh.map_comp_assoc, hh]
    have he := E.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory eG.hom (.up ℤ)).app J)
    simp only [Functor.comp_map] at he
    erw [← reassoc_of% he]
    erw [E.mapDerivedCategoryFactorsh.hom_inv_id_app J, Category.comp_id]
    erw [← E.mapDerivedCategory.map_comp, ha]
  apply (cancel_mono (ib.hom.app (E.mapDerivedCategory.obj K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact congr_app hab K

private theorem derived_horizontal_identity
    {A B : Type v} [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ B) (E : A ⥤ A) (F : B ⥤ B)
    [G.Additive] [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (eE : E ≅ 𝟭 A) (eF : F ≅ 𝟭 B) (δ : G ⋙ F ≅ E ⋙ G)
    (γ : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      E.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hδ : ∀ X, δ.hom.app X ≫ G.map (eE.hom.app X) = eF.hom.app (G.obj X))
    (hγ : ∀ J : HomotopyCategory A (.up ℤ),
      F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app J) ≫
        γ.hom.app (DerivedCategory.Qh.obj J) =
      F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory δ.hom (.up ℤ)).app J) ≫
        G.rightDerivedFunctorUnit.app ((E.mapHomotopyCategory (.up ℤ)).obj J) ≫
        G.rightDerivedFunctor.map (E.mapDerivedCategoryFactorsh.inv.app J))
    (K : DerivedCategory A) :
    γ.hom.app K =
      (Functor.mapDerivedCategoryNatIso eF ≪≫
        Functor.mapDerivedCategoryIdIso B).hom.app (G.rightDerivedFunctor.obj K) ≫
      G.rightDerivedFunctor.map ((Functor.mapDerivedCategoryNatIso eE ≪≫
        Functor.mapDerivedCategoryIdIso A).inv.app K) := by
  let eED := Functor.mapDerivedCategoryNatIso eE ≪≫
    Functor.mapDerivedCategoryIdIso A
  let eFD := Functor.mapDerivedCategoryNatIso eF ≪≫
    Functor.mapDerivedCategoryIdIso B
  let a : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      G.rightDerivedFunctor :=
    γ.hom ≫ Functor.whiskerRight eED.hom G.rightDerivedFunctor
  let b : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      G.rightDerivedFunctor := Functor.whiskerLeft G.rightDerivedFunctor eFD.hom
  have : (G.rightDerivedFunctor ⋙ F.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight G.rightDerivedFunctorUnit F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
        F.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun X => ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    have hi : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj J)) := inferInstance
    change IsIso (F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj J)) ≫ 𝟙 _)
    infer_instance
  have hab : a = b := by
    apply Functor.rightDerived_ext (G.rightDerivedFunctor ⋙ F.mapDerivedCategory)
      (Functor.whiskerRight G.rightDerivedFunctorUnit F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.assoc]
    simp only [Functor.comp_obj]
    erw [Category.id_comp, Category.id_comp]
    erw [reassoc_of% hγ J]
    erw [← G.rightDerivedFunctor.map_comp, exact_identity_fac E eE J,
      Iso.inv_hom_id_app_assoc]
    have hn := G.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory eE.hom (.up ℤ)).app J)
    simp only [Functor.comp_map] at hn
    erw [← hn]
    have hf := eFD.hom.naturality (G.rightDerivedFunctorUnit.app J)
    simp only [Functor.id_map] at hf
    erw [hf, exact_identity_fac F eF ((G.mapHomotopyCategory (.up ℤ)).obj J)]
    have ht : δ.hom ≫ Functor.whiskerRight eE.hom G =
        Functor.whiskerLeft G eF.hom := by
      ext X
      exact hδ X
    have hh := congr_app (congrArg (fun t => NatTrans.mapHomotopyCategory t (.up ℤ)) ht) J
    simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
    change (NatTrans.mapHomotopyCategory δ.hom (.up ℤ)).app J ≫
        (G.mapHomotopyCategory (.up ℤ)).map ((NatTrans.mapHomotopyCategory eE.hom (.up ℤ)).app J) =
      (NatTrans.mapHomotopyCategory eF.hom (.up ℤ)).app
        ((G.mapHomotopyCategory (.up ℤ)).obj J) at hh
    erw [← DerivedCategory.Qh.map_comp_assoc, hh]
    erw [Category.assoc]
    rfl
  apply (cancel_mono (G.rightDerivedFunctor.map (eED.hom.app K))).1
  change γ.hom.app K ≫ G.rightDerivedFunctor.map (eED.hom.app K) =
    (eFD.hom.app (G.rightDerivedFunctor.obj K) ≫
      G.rightDerivedFunctor.map (eED.inv.app K)) ≫
        G.rightDerivedFunctor.map (eED.hom.app K)
  rw [Category.assoc, ← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact congr_app hab K

private theorem derived_identity_fac
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : G ≅ 𝟭 A) (J : HomotopyCategory A (.up ℤ)) :
    G.rightDerivedFunctorUnit.app J ≫
      (G.rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) := by
  have hf := congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac J
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  change G.rightDerivedFunctorUnit.app J ≫
    G.rightDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app _ = _
  rw [← Category.assoc, hf, exact_identity_fac, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.Etale
