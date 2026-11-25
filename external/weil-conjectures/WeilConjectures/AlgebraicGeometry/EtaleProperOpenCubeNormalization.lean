/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import all WeilConjectures.AlgebraicGeometry.DerivedExchangeModuleTermwise
import all WeilConjectures.AlgebraicGeometry.UnboundedProperOpenComposition
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Unbounded proper/open BaseChange

Source: Stacks Project, Tags 0F7F.
-/

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

private def ExactSquareNormalized
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (K : C₀ ⥤ C₁) (D : C₀ ⥤ C₂) (A : C₁ ⥤ C₃) (K' : C₂ ⥤ C₃)
    [K.Additive] [D.Additive] [A.Additive] [K'.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits D] [PreservesFiniteColimits D]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    (β : K ⋙ A ≅ D ⋙ K')
    (b : K.mapDerivedCategory ⋙ A.mapDerivedCategory ≅
      D.mapDerivedCategory ⋙ K'.mapDerivedCategory) : Prop :=
    ∀ X : HomotopyCategory C₀ (.up ℤ),
      b.hom.app (DerivedCategory.Qh.obj X) ≫
        K'.mapDerivedCategory.map (D.mapDerivedCategoryFactorsh.hom.app X) ≫
        K'.mapDerivedCategoryFactorsh.hom.app ((D.mapHomotopyCategory (.up ℤ)).obj X) =
      A.mapDerivedCategory.map (K.mapDerivedCategoryFactorsh.hom.app X) ≫
        A.mapDerivedCategoryFactorsh.hom.app ((K.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X)

private theorem canonical_square_normalized
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (K : C₀ ⥤ C₁) (D : C₀ ⥤ C₂) (A : C₁ ⥤ C₃) (K' : C₂ ⥤ C₃)
    [K.Additive] [D.Additive] [A.Additive] [K'.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits D] [PreservesFiniteColimits D]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    (β : K ⋙ A ≅ D ⋙ K') :
    ExactSquareNormalized K D A K' β
      (Functor.mapDerivedCategoryCompIso K A ≪≫
        Functor.mapDerivedCategoryNatIso β ≪≫ (Functor.mapDerivedCategoryCompIso D K').symm) := by
  intro X
  simpa only [Iso.trans_hom, Iso.symm_hom] using square_factors K D A K' β X

private theorem generic_cube
    {C₀ C₁ C₂ C₃ C₀' C₁' C₂' C₃' : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Category.{w} C₀'] [Category.{w} C₁'] [Category.{w} C₂'] [Category.{w} C₃']
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [Abelian C₀'] [Abelian C₁'] [Abelian C₂'] [Abelian C₃']
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [HasDerivedCategory C₀'] [HasDerivedCategory C₁']
    [HasDerivedCategory C₂'] [HasDerivedCategory C₃']
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    [Abelian.HasKInjectiveResolutions C₀'] [Abelian.HasKInjectiveResolutions C₁']
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (R' : C₀' ⥤ C₂') (P' : C₁' ⥤ C₃')
    (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃) (K' : C₀' ⥤ C₁') (E' : C₂' ⥤ C₃')
    (A : C₁ ⥤ C₁') (B : C₃ ⥤ C₃') (C : C₂ ⥤ C₂') (D : C₀ ⥤ C₀')
    [R.Additive] [P.Additive] [R'.Additive] [P'.Additive]
    [K.Additive] [E.Additive] [K'.Additive] [E'.Additive]
    [A.Additive] [B.Additive] [C.Additive] [D.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits C] [PreservesFiniteColimits C]
    [PreservesFiniteLimits D] [PreservesFiniteColimits D]
    (θ : R ⋙ E ⟶ K ⋙ P) (θ' : R' ⋙ E' ⟶ K' ⋙ P')
    (eP : P ⋙ B ⟶ A ⋙ P') (eR : R ⋙ C ⟶ D ⋙ R')
    (βK : K ⋙ A ≅ D ⋙ K') (βE : E ⋙ B ≅ C ⋙ E')
    (h : ∀ X, B.map (θ.app X) ≫ eP.app (K.obj X) ≫ P'.map (βK.hom.app X) =
      βE.hom.app (R.obj X) ≫ E'.map (eR.app X) ≫ θ'.app (D.obj X))
    (Γ : R.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      K.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (Γ' : R'.rightDerivedFunctor ⋙ E'.mapDerivedCategory ⟶
      K'.mapDerivedCategory ⋙ P'.rightDerivedFunctor)
    (EP : P.rightDerivedFunctor ⋙ B.mapDerivedCategory ⟶
      A.mapDerivedCategory ⋙ P'.rightDerivedFunctor)
    (ER : R.rightDerivedFunctor ⋙ C.mapDerivedCategory ⟶
      D.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hΓ : ProperOpenUnitNormalized R P K E θ Γ)
    (hΓ' : ProperOpenUnitNormalized R' P' K' E' θ' Γ')
    (hEP : ProperOpenUnitNormalized P P' A B eP EP)
    (hER : ProperOpenUnitNormalized R R' D C eR ER)
    (bK : K.mapDerivedCategory ⋙ A.mapDerivedCategory ≅
      D.mapDerivedCategory ⋙ K'.mapDerivedCategory)
    (bE : E.mapDerivedCategory ⋙ B.mapDerivedCategory ≅
      C.mapDerivedCategory ⋙ E'.mapDerivedCategory)
    (hbK : ExactSquareNormalized K D A K' βK bK)
    (hbE : ExactSquareNormalized E C B E' βE bE)
    (X : DerivedCategory C₀) :
    B.mapDerivedCategory.map (Γ.app X) ≫ EP.app (K.mapDerivedCategory.obj X) ≫
        P'.rightDerivedFunctor.map (bK.hom.app X) =
      bE.hom.app (R.rightDerivedFunctor.obj X) ≫
        E'.mapDerivedCategory.map (ER.app X) ≫ Γ'.app (D.mapDerivedCategory.obj X) := by
  unfold ProperOpenUnitNormalized at hΓ hΓ' hEP hER
  unfold ExactSquareNormalized at hbK hbE
  let c₁ : (R.rightDerivedFunctor ⋙ E.mapDerivedCategory) ⋙ B.mapDerivedCategory ⟶
      (D.mapDerivedCategory ⋙ K'.mapDerivedCategory) ⋙ P'.rightDerivedFunctor :=
    Functor.whiskerRight Γ B.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft K.mapDerivedCategory EP ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight bK.hom P'.rightDerivedFunctor
  let c₂ : (R.rightDerivedFunctor ⋙ E.mapDerivedCategory) ⋙ B.mapDerivedCategory ⟶
      (D.mapDerivedCategory ⋙ K'.mapDerivedCategory) ⋙ P'.rightDerivedFunctor :=
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft R.rightDerivedFunctor bE.hom ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ER E'.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft D.mapDerivedCategory Γ' ≫
      (Functor.associator _ _ _).inv
  let α : ((R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E.mapDerivedCategory) ⋙
      B.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ ((R.rightDerivedFunctor ⋙ E.mapDerivedCategory) ⋙
        B.mapDerivedCategory) :=
    Functor.whiskerRight (Functor.whiskerRight R.rightDerivedFunctorUnit
      E.mapDerivedCategory ≫ (Functor.associator _ _ _).hom) B.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  have : ((R.rightDerivedFunctor ⋙ E.mapDerivedCategory) ⋙
      B.mapDerivedCategory).IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso C₀ (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (((R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E.mapDerivedCategory) ⋙
        B.mapDerivedCategory)).isRightDerivedFunctor_of_isIso α (fun Y => ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective Y
    dsimp only [α, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_hom_app]
    have hi : IsIso (R.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C₀ (.up ℤ)).obj J)) := inferInstance
    simp only [Category.comp_id]
    change IsIso (B.mapDerivedCategory.map (E.mapDerivedCategory.map
      (R.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient C₀ (.up ℤ)).obj J))))
    infer_instance
  have hc : c₁ = c₂ := by
    apply Functor.rightDerived_ext _ α (HomotopyCategory.quasiIso C₀ (.up ℤ))
    apply NatTrans.ext
    funext Y
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    let Y := (HomotopyCategory.quotient C₀ (.up ℤ)).obj J
    change _ = _
    simp only [α, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.comp_id, Category.id_comp,
      Functor.comp_obj, Category.assoc]
    erw [← B.mapDerivedCategory.map_comp_assoc, hΓ Y,
      B.mapDerivedCategory.map_comp]
    simp only [B.mapDerivedCategory.map_comp, Category.assoc]
    have nEP := EP.naturality (K.mapDerivedCategoryFactorsh.inv.app Y)
    simp only [Functor.comp_map] at nEP
    erw [reassoc_of% nEP, reassoc_of% hEP ((K.mapHomotopyCategory (.up ℤ)).obj Y)]
    have nβE := bE.hom.naturality (R.rightDerivedFunctorUnit.app Y)
    simp only [Functor.comp_map] at nβE
    erw [reassoc_of% nβE]
    erw [← E'.mapDerivedCategory.map_comp_assoc, hER Y,
      E'.mapDerivedCategory.map_comp]
    simp only [E'.mapDerivedCategory.map_comp, Category.assoc]
    have nΓ' := Γ'.naturality (D.mapDerivedCategoryFactorsh.inv.app Y)
    simp only [Functor.comp_map] at nΓ'
    erw [nΓ', reassoc_of% hΓ' ((D.mapHomotopyCategory (.up ℤ)).obj Y)]
    apply (cancel_mono (P'.rightDerivedFunctor.map
      (K'.mapDerivedCategory.map (D.mapDerivedCategoryFactorsh.hom.app Y) ≫
        K'.mapDerivedCategoryFactorsh.hom.app ((D.mapHomotopyCategory (.up ℤ)).obj Y)))).1
    simp only [P'.rightDerivedFunctor.map_comp, Category.assoc]
    have hK : A.mapDerivedCategoryFactorsh.inv.app
          ((K.mapHomotopyCategory (.up ℤ)).obj Y) ≫
        A.mapDerivedCategory.map (K.mapDerivedCategoryFactorsh.inv.app Y) ≫
        bK.hom.app (DerivedCategory.Qh.obj Y) ≫
        K'.mapDerivedCategory.map (D.mapDerivedCategoryFactorsh.hom.app Y) ≫
        K'.mapDerivedCategoryFactorsh.hom.app ((D.mapHomotopyCategory (.up ℤ)).obj Y) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory βK.hom (.up ℤ)).app Y) := by
      erw [hbK Y]
      erw [← A.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
        A.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    erw [← P'.rightDerivedFunctor.map_comp, ← P'.rightDerivedFunctor.map_comp,
      ← P'.rightDerivedFunctor.map_comp, ← P'.rightDerivedFunctor.map_comp, hK]
    have hD : K'.mapDerivedCategoryFactorsh.inv.app
          ((D.mapHomotopyCategory (.up ℤ)).obj Y) ≫
        K'.mapDerivedCategory.map (D.mapDerivedCategoryFactorsh.inv.app Y) ≫
        K'.mapDerivedCategory.map (D.mapDerivedCategoryFactorsh.hom.app Y) ≫
        K'.mapDerivedCategoryFactorsh.hom.app ((D.mapHomotopyCategory (.up ℤ)).obj Y) =
        𝟙 _ := by
      erw [← K'.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
        K'.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
    simp only [← P'.rightDerivedFunctor.map_comp]
    erw [hD, P'.rightDerivedFunctor.map_id, Category.comp_id]
    have nu := P'.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory βK.hom (.up ℤ)).app Y)
    simp only [Functor.comp_map] at nu
    erw [← nu]
    have ne := E'.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory eR (.up ℤ)).app Y)
    simp only [Functor.comp_map] at ne
    erw [reassoc_of% ne]
    erw [reassoc_of% hbE ((R.mapHomotopyCategory (.up ℤ)).obj Y)]
    have nb := B.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory θ (.up ℤ)).app Y)
    simp only [Functor.comp_map] at nb
    erw [reassoc_of% nb]
    have hh : (B.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory θ (.up ℤ)).app Y) ≫
      (NatTrans.mapHomotopyCategory eP (.up ℤ)).app
        ((K.mapHomotopyCategory (.up ℤ)).obj Y) ≫
      (P'.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory βK.hom (.up ℤ)).app Y) =
      (NatTrans.mapHomotopyCategory βE.hom (.up ℤ)).app
        ((R.mapHomotopyCategory (.up ℤ)).obj Y) ≫
      (E'.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory eR (.up ℤ)).app Y) ≫
      (NatTrans.mapHomotopyCategory θ' (.up ℤ)).app
        ((D.mapHomotopyCategory (.up ℤ)).obj Y) := by
      dsimp only [Y]
      simp only [NatTrans.mapHomotopyCategory_app, HomotopyCategory.quotient_obj_as,
        Functor.mapHomotopyCategory_map, ← Functor.map_comp]
      congr 1
      ext n
      exact h (J.X n)
    erw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc,
      Category.assoc, hh]
    simp only [DerivedCategory.Qh.map_comp, Category.assoc]
    rfl
  simpa only [c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, Functor.comp_obj, Category.assoc] using congr_app hc X

attribute [local irreducible] lowerStar upperStar openImmersionLowerShriek

private theorem ordinary_baseChange_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z X₁ Y₁ Z₁ : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁)
    (a : X₁ ⟶ X) (b : Y₁ ⟶ Y) (c : Z₁ ⟶ Z)
    (sf : CommSq a f₁ f b) (sg : CommSq b g₁ g c)
    (h : X ⟶ Z) (hh : h = f ≫ g) (h₁ : X₁ ⟶ Z₁) (hh₁ : h₁ = f₁ ≫ g₁)
    (s : CommSq a h₁ h c)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (c)^*[ModuleCat.{u + 1} A].map
        ((lowerStarComp (ModuleCat.{u + 1} A) f g h hh).hom.app F) ≫
      (baseChangeMap (ModuleCat.{u + 1} A) s).app F =
    (baseChangeMap (ModuleCat.{u + 1} A) sg).app ((f)_*[ModuleCat.{u + 1} A].obj F) ≫
      (g₁)_*[ModuleCat.{u + 1} A].map
        ((baseChangeMap (ModuleCat.{u + 1} A) sf).app F) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) f₁ g₁ h₁ hh₁).hom.app
        ((a)^*[ModuleCat.{u + 1} A].obj F) := by
  subst h
  subst h₁
  rw [baseChangeMap_paste_vert_app (ModuleCat.{u + 1} A) sf sg s F]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency true in
private theorem ordinary_cube (A : Type (u + 1)) [CommRing A]
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
        (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
        (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
        (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
        (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
    (θ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
      (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (θ₁ : (r₁)_*[ModuleCat.{u + 1} A] ⋙ (i₁)_!open[ModuleCat.{u + 1} A] ≅
      (k₁)_!open[ModuleCat.{u + 1} A] ⋙ (p₁)_*[ModuleCat.{u + 1} A])
    (hθ : ∀ F, θ.hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F)
    (hθ₁ : ∀ F, θ₁.hom.app F ≫
            (p₁)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k₁).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k₁ p₁).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i₁).app
              ((r₁)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r₁ i₁ (k₁ ≫ p₁) sq₁.w).hom.app F)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
        ((b)^*[ModuleCat.{u + 1} A]).map (θ.hom.app F) ≫
            (baseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
              (((k)_!open[ModuleCat.{u + 1} A]).obj F) ≫
            ((p₁)_*[ModuleCat.{u + 1} A]).map
              ((@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
                (ModuleCat.{u + 1} A) sk)).inv.app F) =
          (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
              (ModuleCat.{u + 1} A) si)).inv.app
                (((r)_*[ModuleCat.{u + 1} A]).obj F) ≫
            ((i₁)_!open[ModuleCat.{u + 1} A]).map
              ((baseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app F) ≫
            θ₁.hom.app (((d)^*[ModuleCat.{u + 1} A]).obj F) := by
  let Bk := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sk)
  let Bi := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) si)
  have hb (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      Bk.inv.app G ≫
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k₁).app
          ((d)^*[ModuleCat.{u + 1} A].obj G) =
      (a)^*[ModuleCat.{u + 1} A].map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app G) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) sk.toCommSq).app G := by
    apply (cancel_epi (Bk.hom.app G)).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact (openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
      (ModuleCat.{u + 1} A) sk.toCommSq G).symm
  have hi (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      Bi.inv.app G ≫
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i₁).app
          ((c)^*[ModuleCat.{u + 1} A].obj G) =
      (b)^*[ModuleCat.{u + 1} A].map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app G) ≫
        (baseChangeMap (ModuleCat.{u + 1} A) si.toCommSq).app G := by
    apply (cancel_epi (Bi.hom.app G)).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    exact (openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
      (ModuleCat.{u + 1} A) si.toCommSq G).symm
  let s := sk.toCommSq.vert_comp sp.toCommSq
  have hkp := ordinary_baseChange_comp A k p k₁ p₁ d a b
    sk.toCommSq sp.toCommSq (k ≫ p) rfl (k₁ ≫ p₁) rfl s F
  have hri := ordinary_baseChange_comp A r i r₁ i₁ d c b
    sr.toCommSq si.toCommSq (k ≫ p) sq.w (k₁ ≫ p₁) sq₁.w s F
  have np := (baseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)
  have ni := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i₁).naturality
    ((baseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app F)
  simp only [Functor.comp_map, Functor.comp_obj] at np ni
  have := open_compare_mono A k₁ ((d)^*[ModuleCat.{u + 1} A].obj F)
  apply (cancel_mono ((p₁)_*[ModuleCat.{u + 1} A].map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k₁).app
      ((d)^*[ModuleCat.{u + 1} A].obj F)))).1
  apply (cancel_mono ((lowerStarComp (ModuleCat.{u + 1} A) k₁ p₁).hom.app
    ((d)^*[ModuleCat.{u + 1} A].obj F))).1
  simp only [Category.assoc]
  have hbm := congrArg ((p₁)_*[ModuleCat.{u + 1} A].map) (hb F)
  simp only [CategoryTheory.Functor.map_comp] at hbm
  erw [reassoc_of% hbm]
  erw [← reassoc_of% np]
  rw [← hkp]
  have htm := congrArg ((b)^*[ModuleCat.{u + 1} A].map) (hθ F)
  simp only [CategoryTheory.Functor.map_comp] at htm
  rw [reassoc_of% htm]
  rw [hri]
  rw [← reassoc_of% hi]
  rw [← reassoc_of% ni]
  have ht := hθ₁ ((d)^*[ModuleCat.{u + 1} A].obj F)
  rw [ht]

private theorem derived_mate_unit
    {C₁ C₂ C₃ C₄ : Type v}
    [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃] [Category.{w} C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ H)
 :
    ProperOpenUnitNormalized R R' H G
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom))
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
          Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso L H).symm).hom)) := by
  intro X
  exact Adjunction.derivedExact_mateEquiv_app_fac adj adj'
    (TwoSquare.mk _ _ _ _ e.hom)
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso L H).symm).hom)
    (by
      intro N
      simpa only [Iso.trans_hom, Iso.symm_hom] using square_factors G L L' H e N) X

private theorem exact_exchange_normalized (A : Type (u + 1)) [CommRing A]
    {X Y X₁ Y₁ : Scheme.{u}}
    (f : X ⟶ Y) (f₁ : X₁ ⟶ Y₁) (a : X₁ ⟶ X) (b : Y₁ ⟶ Y)
    (s : CommSq a f₁ f b) :
    ProperOpenUnitNormalized
      (f)_*[ModuleCat.{u + 1} A] (f₁)_*[ModuleCat.{u + 1} A]
      (a)^*[ModuleCat.{u + 1} A] (b)^*[ModuleCat.{u + 1} A]
      (baseChangeMap (ModuleCat.{u + 1} A) s)
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) s) := by
  exact derived_mate_unit
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f₁)
    (squareUpperStarIso (ModuleCat.{u + 1} A) s)

private theorem map_derived_iso_symm
    {C D : Type v} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_symm e

private theorem open_baseChange_factors (A : Type (u + 1)) [CommRing A]
    {U V U₁ V₁ : Scheme.{u}} (k : U ⟶ V) (k₁ : U₁ ⟶ V₁)
    (d : U₁ ⟶ U) (a : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion k₁] (s : IsPullback d k₁ k a) :
    ExactSquareNormalized
      (k)_!open[ModuleCat.{u + 1} A] (d)^*[ModuleCat.{u + 1} A]
      (a)^*[ModuleCat.{u + 1} A] (k₁)_!open[ModuleCat.{u + 1} A]
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} A) s)).symm
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) s).symm := by
  simpa only [mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    Iso.symm_inv, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
    map_derived_iso_symm] using
    canonical_square_normalized
      (k)_!open[ModuleCat.{u + 1} A] (d)^*[ModuleCat.{u + 1} A]
      (a)^*[ModuleCat.{u + 1} A] (k₁)_!open[ModuleCat.{u + 1} A]
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} A) s)).symm

/-- Base change for support- and right-derived-unit-normalized comparison families.
Source: Stacks Project, Tag 0F7F.
(auxiliary; not a blueprint node).

Proof:
First prove the ordinary sheaf cube. Postcompose with the monic open-to-direct-image
comparison and its compositors. The support equations replace both theta maps by
inclusions in the common direct image. Compatibility of open base change with those
inclusions and ordinary exchange pasting give the same map, so monicity gives the cube.
For a generic cube of additive functors with exact horizontal functors, the source
right-derived functor followed by the two exact derived functors is again right-derived:
its unit is an isomorphism on K-injectives. Right-derived extensionality therefore
reduces the desired equality to precomposition with that unit. Insert the four unit
normalizations, the two exact base-change factorization equations, and naturality.
The remaining equality is the homotopy-category image of the ordinary cube, checked
on complexes in each degree. The exact adjunction-mate formula gives the required
unit equations for the specified exchanges; square factorization gives those for the
specified inverse open-base-change maps. Apply the generic result to the sheaf cube.
No exchange is inverted or cancelled, and inverse image need not preserve K-injectives.
-/
theorem etaleProperOpenCubeNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (θ : ∀ {U V W Z : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (Γ : ∀ {U V W Z : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
        (_sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))
    (hθ : (∀ {U V W Z : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F))
    (hΓ : ∀ {U V W Z : Scheme.{u}}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
      (sq : CommSq k r p i),
      ProperOpenUnitNormalized
        (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
        (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
        (θ k r p i sq).hom (Γ k r p i sq).hom) :
    (∀ {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
        (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
        (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
        (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
        (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
        (K : DerivedCategoryModule A U),
        D((b)^*[ModuleCat.{u + 1} A]).map ((Γ k r p i sq).hom.app K) ≫
            (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₁)_*[ModuleCat.{u + 1} A]).map
              ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
                (ModuleCat.{u + 1} A) sk).inv.app K) =
          (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) si).inv.app
                (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((i₁)_!open[ModuleCat.{u + 1} A]).map
              ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app K) ≫
            (Γ k₁ r₁ p₁ i₁ sq₁).hom.app (D((d)^*[ModuleCat.{u + 1} A]).obj K))  := by
  intro U V W Z U₁ V₁ W₁ Z₁ k r p i k₁ r₁ p₁ i₁
    _ _ _ _ _ _ _ _ sq sq₁ a b c d sp sr si sk M
  exact generic_cube
    (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
    (r₁)_*[ModuleCat.{u + 1} A] (p₁)_*[ModuleCat.{u + 1} A]
    (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
    (k₁)_!open[ModuleCat.{u + 1} A] (i₁)_!open[ModuleCat.{u + 1} A]
    (a)^*[ModuleCat.{u + 1} A] (b)^*[ModuleCat.{u + 1} A]
    (c)^*[ModuleCat.{u + 1} A] (d)^*[ModuleCat.{u + 1} A]
    (θ k r p i sq).hom (θ k₁ r₁ p₁ i₁ sq₁).hom
    (baseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq)
    (baseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} A) sk)).symm
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} A) si)).symm
    (ordinary_cube A k r p i k₁ r₁ p₁ i₁ sq sq₁ a b c d sp sr si sk
      (θ k r p i sq) (θ k₁ r₁ p₁ i₁ sq₁)
      (hθ k r p i sq) (hθ k₁ r₁ p₁ i₁ sq₁))
    (Γ k r p i sq).hom (Γ k₁ r₁ p₁ i₁ sq₁).hom
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq)
    (hΓ k r p i sq) (hΓ k₁ r₁ p₁ i₁ sq₁)
    (exact_exchange_normalized A p p₁ a b sp.toCommSq)
    (exact_exchange_normalized A r r₁ d c sr.toCommSq)
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) sk).symm
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) si).symm
    (open_baseChange_factors A k k₁ d a sk)
    (open_baseChange_factors A i i₁ c b si) M

end AlgebraicGeometry.Etale
