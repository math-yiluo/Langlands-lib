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
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-! Horizontal composition of unbounded proper/open interchange, Stacks Tag 0F7D. -/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private lemma derived_horizontal_factor
    {C D E : Type v} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (X : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
        (DerivedCategory.Qh.obj X) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app X) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj X) =
    H.mapDerivedCategoryFactorsh.hom.app X ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh F G X]
  exact Functor.mapDerivedCategoryNatIso_fach e X

/-- A comparison is normalized when it carries the right-derived units to the
termwise ordinary comparison and the target right-derived unit.
Source: Stacks Project, Tag 0F7D.
(auxiliary; not a blueprint node). -/
def ProperOpenUnitNormalized
    {C C' D D' : Type v} [Category.{w} C] [Category.{w} C']
    [Category.{w} D] [Category.{w} D']
    [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [HasDerivedCategory D] [HasDerivedCategory D']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (G : C ⥤ D) (H : C' ⥤ D') (E : C ⥤ C') (F : D ⥤ D')
    [G.Additive] [H.Additive] [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : G ⋙ F ⟶ E ⋙ H)
    (c : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      E.mapDerivedCategory ⋙ H.rightDerivedFunctor) : Prop :=
    ∀ X : HomotopyCategory C (.up ℤ),
      F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app X) ≫
        c.app (DerivedCategory.Qh.obj X) =
      F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e (.up ℤ)).app X) ≫
        H.rightDerivedFunctorUnit.app ((E.mapHomotopyCategory (.up ℤ)).obj X) ≫
        H.rightDerivedFunctor.map (E.mapDerivedCategoryFactorsh.inv.app X)

attribute [local instance 2000] Abelian.toPreadditive

private lemma generic_horizontal_pasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type v}
    [Category.{w} A₀] [Category.{w} A₁] [Category.{w} A₂]
    [Category.{w} B₀] [Category.{w} B₁] [Category.{w} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
    [Abelian.HasKInjectiveResolutions A₀] [Abelian.HasKInjectiveResolutions A₁]
    [Abelian.HasKInjectiveResolutions A₂]
    (G : A₀ ⥤ B₀) (H : A₁ ⥤ B₁) (I : A₂ ⥤ B₂)
    (E₀ : A₀ ⥤ A₁) (F₀ : A₁ ⥤ A₂) (E : A₀ ⥤ A₂)
    (E₁ : B₀ ⥤ B₁) (F₁ : B₁ ⥤ B₂) (F : B₀ ⥤ B₂)
    [G.Additive] [H.Additive] [I.Additive]
    [E₀.Additive] [F₀.Additive] [E.Additive]
    [E₁.Additive] [F₁.Additive] [F.Additive]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : E ≅ E₀ ⋙ F₀) (b : F ≅ E₁ ⋙ F₁)
    (e₁ : G ⋙ E₁ ⟶ E₀ ⋙ H) (e₂ : H ⋙ F₁ ⟶ F₀ ⋙ I)
    (e : G ⋙ F ⟶ E ⋙ I)
    (he : ∀ X, e.app X ≫ I.map (a.hom.app X) =
      b.hom.app (G.obj X) ≫ F₁.map (e₁.app X) ≫ e₂.app (E₀.obj X))
    (c₁ : G.rightDerivedFunctor ⋙ E₁.mapDerivedCategory ⟶
      E₀.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (c₂ : H.rightDerivedFunctor ⋙ F₁.mapDerivedCategory ⟶
      F₀.mapDerivedCategory ⋙ I.rightDerivedFunctor)
    (c : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      E.mapDerivedCategory ⋙ I.rightDerivedFunctor)
    (hc₁ : ProperOpenUnitNormalized G H E₀ E₁ e₁ c₁)
    (hc₂ : ProperOpenUnitNormalized H I F₀ F₁ e₂ c₂)
    (hc : ProperOpenUnitNormalized G I E F e c)
    (da : E.mapDerivedCategory ≅ E₀.mapDerivedCategory ⋙ F₀.mapDerivedCategory)
    (db : F.mapDerivedCategory ≅ E₁.mapDerivedCategory ⋙ F₁.mapDerivedCategory)
    (hfa : ∀ X : HomotopyCategory A₀ (.up ℤ),
      da.hom.app (DerivedCategory.Qh.obj X) ≫
        F₀.mapDerivedCategory.map (E₀.mapDerivedCategoryFactorsh.hom.app X) ≫
        F₀.mapDerivedCategoryFactorsh.hom.app ((E₀.mapHomotopyCategory (.up ℤ)).obj X) =
      E.mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app X))
    (hfb : ∀ X : HomotopyCategory B₀ (.up ℤ),
      db.hom.app (DerivedCategory.Qh.obj X) ≫
        F₁.mapDerivedCategory.map (E₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        F₁.mapDerivedCategoryFactorsh.hom.app ((E₁.mapHomotopyCategory (.up ℤ)).obj X) =
      F.mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory b.hom (.up ℤ)).app X))
    (K : DerivedCategory A₀) :
    c.app K =
      db.hom.app (G.rightDerivedFunctor.obj K) ≫
      F₁.mapDerivedCategory.map (c₁.app K) ≫
      c₂.app (E₀.mapDerivedCategory.obj K) ≫
      I.rightDerivedFunctor.map (da.inv.app K) := by
  unfold ProperOpenUnitNormalized at hc₁ hc₂ hc
  let ca : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      (E₀.mapDerivedCategory ⋙ F₀.mapDerivedCategory) ⋙ I.rightDerivedFunctor :=
    c ≫ Functor.whiskerRight da.hom I.rightDerivedFunctor
  let cb : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      (E₀.mapDerivedCategory ⋙ F₀.mapDerivedCategory) ⋙ I.rightDerivedFunctor :=
    Functor.whiskerLeft G.rightDerivedFunctor db.hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight c₁ F₁.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft E₀.mapDerivedCategory c₂ ≫
      (Functor.associator _ _ _).inv
  have : (G.rightDerivedFunctor ⋙ F.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight G.rightDerivedFunctorUnit F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A₀ (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
        F.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun X ↦ ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    have hi : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A₀ (.up ℤ)).obj J)) := inferInstance
    change IsIso (F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A₀ (.up ℤ)).obj J)) ≫ 𝟙 _)
    infer_instance
  have hab : ca = cb := by
    apply Functor.rightDerived_ext (G.rightDerivedFunctor ⋙ F.mapDerivedCategory)
      (Functor.whiskerRight G.rightDerivedFunctorUnit F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A₀ (.up ℤ))
    apply NatTrans.ext
    funext X
    simp only [ca, cb, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Category.assoc]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
    erw [reassoc_of% hc X]
    have hn := db.hom.naturality (G.rightDerivedFunctorUnit.app X)
    simp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    erw [← F₁.mapDerivedCategory.map_comp_assoc, hc₁ X]
    simp only [F₁.mapDerivedCategory.map_comp, Category.assoc]
    have hn₂ := c₂.naturality (E₀.mapDerivedCategoryFactorsh.inv.app X)
    simp only [Functor.comp_map] at hn₂
    erw [reassoc_of% hn₂, reassoc_of% hc₂ ((E₀.mapHomotopyCategory (.up ℤ)).obj X)]
    apply (cancel_mono (I.rightDerivedFunctor.map
      (F₀.mapDerivedCategory.map (E₀.mapDerivedCategoryFactorsh.hom.app X) ≫
        F₀.mapDerivedCategoryFactorsh.hom.app ((E₀.mapHomotopyCategory (.up ℤ)).obj X)))).1
    simp only [I.rightDerivedFunctor.map_comp, Category.assoc]
    erw [← I.rightDerivedFunctor.map_comp, ← I.rightDerivedFunctor.map_comp]
    have hda : E.mapDerivedCategoryFactorsh.inv.app X ≫ da.hom.app
        (DerivedCategory.Qh.obj X) ≫
        F₀.mapDerivedCategory.map (E₀.mapDerivedCategoryFactorsh.hom.app X) ≫
        F₀.mapDerivedCategoryFactorsh.hom.app ((E₀.mapHomotopyCategory (.up ℤ)).obj X) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app X) := by
      apply (cancel_epi (E.mapDerivedCategoryFactorsh.hom.app X)).1
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      simpa only [Category.assoc] using hfa X
    erw [← I.rightDerivedFunctor.map_comp, hda]
    simp only [Category.id_comp, ← I.rightDerivedFunctor.map_comp]
    erw [← F₀.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
      F₀.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
      I.rightDerivedFunctor.map_id, Category.comp_id]
    have hna := I.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app X)
    simp only [Functor.comp_map] at hna
    erw [← hna]
    have hnb := hfb ((G.mapHomotopyCategory (.up ℤ)).obj X)
    have hne := F₁.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app X)
    simp only [Functor.comp_map] at hne
    erw [reassoc_of% hne]
    erw [reassoc_of% hnb]
    have ht : e ≫ Functor.whiskerRight a.hom I =
        Functor.whiskerLeft G b.hom ≫
          Functor.whiskerRight e₁ F₁ ≫ Functor.whiskerLeft E₀ e₂ := by
      ext Y
      exact he Y
    have hh := congr_app
      (congrArg (fun t => NatTrans.mapHomotopyCategory t (.up ℤ)) ht) X
    simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
    change (NatTrans.mapHomotopyCategory e (.up ℤ)).app X ≫
        (I.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app X) =
      (NatTrans.mapHomotopyCategory b.hom (.up ℤ)).app
          ((G.mapHomotopyCategory (.up ℤ)).obj X) ≫
        (F₁.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory e₁ (.up ℤ)).app X) ≫
        (NatTrans.mapHomotopyCategory e₂ (.up ℤ)).app
          ((E₀.mapHomotopyCategory (.up ℤ)).obj X) at hh
    erw [← DerivedCategory.Qh.map_comp_assoc, hh]
    simp only [DerivedCategory.Qh.map_comp, Category.assoc]
    rfl
  change c.app K = db.hom.app (G.rightDerivedFunctor.obj K) ≫
    F₁.mapDerivedCategory.map (c₁.app K) ≫ c₂.app (E₀.mapDerivedCategory.obj K) ≫
      I.rightDerivedFunctor.map (da.inv.app K)
  apply (cancel_mono (I.rightDerivedFunctor.map (da.hom.app K))).1
  simp only [Category.assoc, ← I.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app]
  erw [I.rightDerivedFunctor.map_id, Category.comp_id]
  simpa only [ca, cb, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.assoc, Category.id_comp,
    Functor.comp_obj, Category.comp_id] using congr_app hab K

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

private theorem open_compare_comp (A : Type (u + 1)) [CommRing A]
    {U V W : Scheme.{u}} (k : U ⟶ V) (i : V ⟶ W)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (k ≫ i)).app F =
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k i).hom.app F ≫
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
          ((k)_!open[ModuleCat.{u + 1} A].obj F) ≫
        (i)_*[ModuleCat.{u + 1} A].map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) k i).hom.app F := by
  apply openImmersionLowerShriek_lowerStar_hom_ext
  rw [unit_map_openImmersionLowerShriekToLowerStar_app_counit]
  symm
  simp only [Functor.map_comp, Category.assoc]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (k ≫ i))
    (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)).ofNatIsoRight
        (upperStarComp (ModuleCat.{u + 1} A) k i).symm) F
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Adjunction.comp_unit_app,
    Functor.comp_obj] at hu
  erw [← Category.assoc, hu]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc]
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  erw [upperStarComp_inv_app_counit_app (ModuleCat.{u + 1} A) k i F]
  simp only [Functor.comp_map]
  have hh := (lowerStarComp (ModuleCat.{u + 1} A) k i).hom_inv_id_app F
  have hhh := congrArg (fun f =>
    (k)^*[ModuleCat.{u + 1} A].map ((i)^*[ModuleCat.{u + 1} A].map f)) hh
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at hhh
  rw [reassoc_of% hhh]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hkn := congrArg (fun f => (k)^*[ModuleCat.{u + 1} A].map f) hn
  simp only [Functor.map_comp] at hkn
  rw [reassoc_of% hkn]
  have hz := congrArg (fun f => (k)^*[ModuleCat.{u + 1} A].map f)
    (unit_map_openImmersionLowerShriekToLowerStar_app_counit
      (ModuleCat.{u + 1} A) i ((k)_!open[ModuleCat.{u + 1} A].obj F))
  simp only [Functor.map_comp] at hz
  erw [reassoc_of% hz, (k)^*[ModuleCat.{u + 1} A].map_id, Category.id_comp,
    unit_map_openImmersionLowerShriekToLowerStar_app_counit]

private theorem ordinary_horizontal (A : Type (u + 1)) [CommRing A]
    {U V T W Z S : Scheme.{u}}
    (k : U ⟶ V) (l : V ⟶ T) (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ S)
    (i : W ⟶ Z) (j : Z ⟶ S)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [IsProper r] [IsProper p] [IsProper q]
    (sq₁ : CommSq k r p i) (sq₂ : CommSq l p q j)
    (θ₁ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
      (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (θ₂ : (p)_*[ModuleCat.{u + 1} A] ⋙ (j)_!open[ModuleCat.{u + 1} A] ≅
      (l)_!open[ModuleCat.{u + 1} A] ⋙ (q)_*[ModuleCat.{u + 1} A])
    (θ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i ≫ j)_!open[ModuleCat.{u + 1} A] ≅
      (k ≫ l)_!open[ModuleCat.{u + 1} A] ⋙ (q)_*[ModuleCat.{u + 1} A])
    (h₁ : ∀ F, θ₁.hom.app F ≫
      (p)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq₁.w).hom.app F)
    (h₂ : ∀ F, θ₂.hom.app F ≫
      (q)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) l).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) l q).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app
        ((p)_*[ModuleCat.{u + 1} A].obj F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) p j (l ≫ q) sq₂.w).hom.app F)
    (h : ∀ F, θ.hom.app F ≫
      (q)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (k ≫ l)).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) (k ≫ l) q).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (i ≫ j)).app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) r (i ≫ j) ((k ≫ l) ≫ q)
        (sq₁.horiz_comp sq₂).w).hom.app F)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    θ.hom.app F ≫ (q)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k l).hom.app F) =
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j).hom.app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (j)_!open[ModuleCat.{u + 1} A].map (θ₁.hom.app F) ≫
      θ₂.hom.app ((k)_!open[ModuleCat.{u + 1} A].obj F) := by
  have := open_compare_mono A k F
  have := open_compare_mono A l ((k)_!open[ModuleCat.{u + 1} A].obj F)
  apply (cancel_mono (
    (q)_*[ModuleCat.{u + 1} A].map
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) l).app
        ((k)_!open[ModuleCat.{u + 1} A].obj F)) ≫
    (q)_*[ModuleCat.{u + 1} A].map
      ((l)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)) ≫
    (q)_*[ModuleCat.{u + 1} A].map
      ((lowerStarComp (ModuleCat.{u + 1} A) k l).hom.app F) ≫
    (lowerStarComp (ModuleCat.{u + 1} A) (k ≫ l) q).hom.app F)).1
  simp only [Category.assoc]
  have hc := congrArg (fun f => (q)_*[ModuleCat.{u + 1} A].map f)
    (open_compare_comp A k l F)
  simp only [Functor.map_comp] at hc
  rw [← reassoc_of% hc, h]
  rw [open_compare_comp A i j ((r)_*[ModuleCat.{u + 1} A].obj F)]
  simp only [Category.assoc]
  apply (cancel_epi ((openImmersionLowerShriekComp
    (ModuleCat.{u + 1} A) i j).hom.app ((r)_*[ModuleCat.{u + 1} A].obj F))).2
  have hkl := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} A) k l q
    (k ≫ l) (l ≫ q) ((k ≫ l) ≫ q) rfl rfl rfl) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hkl
  rw [hkl]
  have nlq := (lowerStarComp (ModuleCat.{u + 1} A) l q).hom.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)
  simp only [Functor.comp_map] at nlq
  rw [reassoc_of% nlq, reassoc_of% h₂ ((k)_!open[ModuleCat.{u + 1} A].obj F)]
  have nj := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).naturality
    (θ₁.hom.app F)
  rw [reassoc_of% nj]
  have npj := (lowerStarComp (ModuleCat.{u + 1} A) p j (l ≫ q) sq₂.w).hom.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)
  simp only [Functor.comp_map] at npj
  rw [← reassoc_of% npj]
  have hkpj := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} A) k p j
    (k ≫ p) (l ≫ q) ((k ≫ l) ≫ q) rfl sq₂.w
    (by simp only [Category.assoc, sq₂.w])) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hkpj
  rw [← hkpj, ← (j)_*[ModuleCat.{u + 1} A].map_comp_assoc,
    ← (j)_*[ModuleCat.{u + 1} A].map_comp_assoc]
  simp only [Category.assoc]
  rw [h₁ F]
  rw [(j)_*[ModuleCat.{u + 1} A].map_comp]
  simp only [Category.assoc]
  have hrij := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} A) r i j
    (k ≫ p) (i ≫ j) ((k ≫ l) ≫ q) sq₁.w rfl
    (by simp only [Category.assoc, sq₂.w])) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hrij
  rw [hrij]

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorObjQIso Functor.mapDerivedCategoryNatIso

set_option backward.isDefEq.respectTransparency true in
/-- Horizontal pasting for normalized unbounded proper/open comparison families.
Source: Stacks Project, Tag 0F7D.
(auxiliary; not a blueprint node).

Proof:
Take a K-injective representative J and resolutions rho:k!J→I and sigma:l!I→H.
Exactness of l! makes sigma after l!rho a resolution of l!k!J. The two consecutive
interchanges are represented by j!(p*rho after theta1), followed by q*sigma after theta2.
Naturality of theta2 moves rho through this expression. Include the remaining sheaf
maps into the common composite direct image using the given support normalizations.
Associativity of support composition identifies their product with the outer theta,
with the open-extension compositors inserted. Their termwise derived descents identify
the chosen composite resolution with the outer one. Equivalently, precompose with the
right-derived unit, use both assumed unit equations, and apply the universal property
of right derivation to the equality of the sheaf maps. This proves the equation for
every derived object without a boundedness assumption.
-/
theorem etaleProperOpenHorizontalNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V T W Z S : Scheme.{u}}
    (k : U ⟶ V) (l : V ⟶ T) (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ S)
    (i : W ⟶ Z) (j : Z ⟶ S)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [IsProper r] [IsProper p] [IsProper q]
    (sq₁ : CommSq k r p i) (sq₂ : CommSq l p q j)
    (θ₁ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
      (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (θ₂ : (p)_*[ModuleCat.{u + 1} A] ⋙ (j)_!open[ModuleCat.{u + 1} A] ≅
      (l)_!open[ModuleCat.{u + 1} A] ⋙ (q)_*[ModuleCat.{u + 1} A])
    (θ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i ≫ j)_!open[ModuleCat.{u + 1} A] ≅
      (k ≫ l)_!open[ModuleCat.{u + 1} A] ⋙ (q)_*[ModuleCat.{u + 1} A])
    (h₁ : ∀ F, θ₁.hom.app F ≫
      (p)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq₁.w).hom.app F)
    (h₂ : ∀ F, θ₂.hom.app F ≫
      (q)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) l).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) l q).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app
        ((p)_*[ModuleCat.{u + 1} A].obj F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) p j (l ≫ q) sq₂.w).hom.app F)
    (h : ∀ F, θ.hom.app F ≫
      (q)_*[ModuleCat.{u + 1} A].map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (k ≫ l)).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) (k ≫ l) q).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (i ≫ j)).app
        ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) r (i ≫ j) ((k ≫ l) ≫ q)
        (sq₁.horiz_comp sq₂).w).hom.app F)
    (Γ₁ : R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))
    (Γ₂ : R((p)_*[ModuleCat.{u + 1} A]) ⋙ D((j)_!open[ModuleCat.{u + 1} A]) ≅
      D((l)_!open[ModuleCat.{u + 1} A]) ⋙ R((q)_*[ModuleCat.{u + 1} A]))
    (Γ : R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i ≫ j)_!open[ModuleCat.{u + 1} A]) ≅
      D((k ≫ l)_!open[ModuleCat.{u + 1} A]) ⋙ R((q)_*[ModuleCat.{u + 1} A]))
    (hΓ₁ : ProperOpenUnitNormalized
      (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
      (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A] θ₁.hom Γ₁.hom)
    (hΓ₂ : ProperOpenUnitNormalized
      (p)_*[ModuleCat.{u + 1} A] (q)_*[ModuleCat.{u + 1} A]
      (l)_!open[ModuleCat.{u + 1} A] (j)_!open[ModuleCat.{u + 1} A] θ₂.hom Γ₂.hom)
    (hΓ : ProperOpenUnitNormalized
      (r)_*[ModuleCat.{u + 1} A] (q)_*[ModuleCat.{u + 1} A]
      (k ≫ l)_!open[ModuleCat.{u + 1} A] (i ≫ j)_!open[ModuleCat.{u + 1} A] θ.hom Γ.hom)
    (K : DerivedCategoryModule A U) :
    Γ.hom.app K =
          (Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((j)_!open[ModuleCat.{u + 1} A]).map (Γ₁.hom.app K) ≫
            Γ₂.hom.app (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((q)_*[ModuleCat.{u + 1} A]).map
              ((Functor.mapDerivedCategoryNatIso
                  (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k l) ≪≫
                (Functor.mapDerivedCategoryCompIso _ _).symm).inv.app K) := by
  have ho := ordinary_horizontal A k l r p q i j sq₁ sq₂ θ₁ θ₂ θ h₁ h₂ h
  exact generic_horizontal_pasting
    (A₀ := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (A₁ := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (A₂ := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B₀ := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B₁ := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B₂ := Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
    (q)_*[ModuleCat.{u + 1} A]
    (k)_!open[ModuleCat.{u + 1} A] (l)_!open[ModuleCat.{u + 1} A]
    (k ≫ l)_!open[ModuleCat.{u + 1} A]
    (i)_!open[ModuleCat.{u + 1} A] (j)_!open[ModuleCat.{u + 1} A]
    (i ≫ j)_!open[ModuleCat.{u + 1} A]
    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k l)
    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j)
    θ₁.hom θ₂.hom
    θ.hom
    ho
    Γ₁.hom Γ₂.hom
    Γ.hom
    hΓ₁ hΓ₂
    hΓ
    (Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k l) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (fun X => derived_horizontal_factor _ _ _ _ X)
    (fun X => derived_horizontal_factor _ _ _ _ X) K

end AlgebraicGeometry.Etale
