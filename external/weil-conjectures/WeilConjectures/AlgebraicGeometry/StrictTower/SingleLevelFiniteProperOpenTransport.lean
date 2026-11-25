/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteCoefficientClopenAlpha
import all WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateSiteTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality
import all WeilConjectures.CategoryTheory.RightDerivedPlusCube
import all WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import all WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization

/-! # Finite coefficient transport of the single-level proper/open mate

This is the coefficient-realization step between the finite site comparison and
strict-tower evaluation. It contains no strict-tower object or evaluation functor.

Source: Stacks Project, Tags 03DA, 07A7, 099R and 09AF
(blueprint: lem-cbc-single-level-finite-proper-open-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

private theorem exactPlusNatIso_symm
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (cancel_mono ((Functor.mapDerivedCategoryPlusNatIso e).hom.app X)).1
  simp only [Iso.symm_hom, Iso.inv_hom_id_app]
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.mapDerivedCategoryNatIso_symm, Iso.inv_hom_id_app]
  exact ((DerivedCategory.Plus.ι (C := D)).map_id
    (G.mapDerivedCategoryPlus.obj X)).symm

private theorem exactPlusMap_ι
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    {X Y : DerivedCategory.Plus C} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

private theorem homotopyPlus_whiskerRight_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive]
    (τ : F₁ ⟶ F₂) (G : D ⥤ E) [G.Additive] (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight τ G)).app K =
      G.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus τ).app K) := by
  have h := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerRight_app τ G K
  simp only [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app] at h
  erw [Category.id_comp, Category.comp_id] at h
  exact h

private theorem homotopyPlus_whiskerLeft_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) [F.Additive] {G₁ G₂ : D ⥤ E} [G₁.Additive] [G₂.Additive]
    (τ : G₁ ⟶ G₂) (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft F τ)).app K =
      (NatTrans.mapHomotopyCategoryPlus τ).app (F.mapHomotopyCategoryPlus.obj K) := by
  have h := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerLeft_app F τ K
  simp only [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app] at h
  erw [Category.id_comp, Category.comp_id] at h
  exact h

private theorem exactAlphaCube
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*}
    [Category* A₁] [Category* A₂] [Category* A₃] [Category* A₄]
    [Category* B₁] [Category* B₂] [Category* B₃] [Category* B₄]
    [Abelian A₁] [Abelian A₂] [Abelian A₃] [Abelian A₄]
    [Abelian B₁] [Abelian B₂] [Abelian B₃] [Abelian B₄]
    [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory A₃] [HasDerivedCategory A₄]
    [HasDerivedCategory B₁] [HasDerivedCategory B₂] [HasDerivedCategory B₃] [HasDerivedCategory B₄]
    (G : A₁ ⥤ A₂) (F : A₁ ⥤ A₃) (Q : A₂ ⥤ A₄) (J : A₃ ⥤ A₄)
    (G' : B₁ ⥤ B₂) (F' : B₁ ⥤ B₃) (Q' : B₂ ⥤ B₄) (J' : B₃ ⥤ B₄)
    (A : A₁ ⥤ B₁) (C : A₂ ⥤ B₂) (E : A₃ ⥤ B₃) (D : A₄ ⥤ B₄)
    [G.Additive] [Limits.PreservesFiniteLimits G]
    [Limits.PreservesFiniteColimits G]
    [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    [Q.Additive] [Limits.PreservesFiniteLimits Q]
    [Limits.PreservesFiniteColimits Q]
    [J.Additive] [Limits.PreservesFiniteLimits J]
    [Limits.PreservesFiniteColimits J]
    [G'.Additive] [Limits.PreservesFiniteLimits G']
    [Limits.PreservesFiniteColimits G']
    [F'.Additive] [Limits.PreservesFiniteLimits F']
    [Limits.PreservesFiniteColimits F']
    [Q'.Additive] [Limits.PreservesFiniteLimits Q']
    [Limits.PreservesFiniteColimits Q']
    [J'.Additive] [Limits.PreservesFiniteLimits J']
    [Limits.PreservesFiniteColimits J']
    [A.Additive] [Limits.PreservesFiniteLimits A]
    [Limits.PreservesFiniteColimits A]
    [C.Additive] [Limits.PreservesFiniteLimits C]
    [Limits.PreservesFiniteColimits C]
    [E.Additive] [Limits.PreservesFiniteLimits E]
    [Limits.PreservesFiniteColimits E]
    [D.Additive] [Limits.PreservesFiniteLimits D]
    [Limits.PreservesFiniteColimits D]
    (e : G ⋙ Q ⟶ F ⋙ J) (e' : G' ⋙ Q' ⟶ F' ⋙ J')
    (a : G ⋙ C ≅ A ⋙ G') (b : J ⋙ D ≅ E ⋙ J')
    (c : C ⋙ Q' ≅ Q ⋙ D) (d : A ⋙ F' ≅ F ⋙ E)
    (h : ∀ N : A₁, D.map (e.app N) ≫ b.hom.app (F.obj N) ≫ J'.map (d.inv.app N) =
      c.inv.app (G.obj N) ≫ Q'.map (a.hom.app N) ≫ e'.app (A.obj N))
    (M : DerivedCategory.Plus A₁) :
    let da := (Functor.mapDerivedCategoryPlusCompIso G C).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso a ≪≫ Functor.mapDerivedCategoryPlusCompIso A G'
    let db := (Functor.mapDerivedCategoryPlusCompIso J D).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso b ≪≫ Functor.mapDerivedCategoryPlusCompIso E J'
    let dc := (Functor.mapDerivedCategoryPlusCompIso C Q').symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso c ≪≫ Functor.mapDerivedCategoryPlusCompIso Q D
    let dd := (Functor.mapDerivedCategoryPlusCompIso A F').symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso d ≪≫ Functor.mapDerivedCategoryPlusCompIso F E
    D.mapDerivedCategoryPlus.map
        ((Etale.ClopenMateNormalization.clopenLocalizedSquarePlus e).app M) ≫
      db.hom.app (F.mapDerivedCategoryPlus.obj M) ≫
      J'.mapDerivedCategoryPlus.map (dd.inv.app M) =
    dc.inv.app (G.mapDerivedCategoryPlus.obj M) ≫
      Q'.mapDerivedCategoryPlus.map (da.hom.app M) ≫
      (Etale.ClopenMateNormalization.clopenLocalizedSquarePlus e').app
        (A.mapDerivedCategoryPlus.obj M) := by
  dsimp only
  let de := Etale.ClopenMateNormalization.clopenLocalizedSquarePlus e
  let de' := Etale.ClopenMateNormalization.clopenLocalizedSquarePlus e'
  let da := (Functor.mapDerivedCategoryPlusCompIso G C).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso a ≪≫ Functor.mapDerivedCategoryPlusCompIso A G'
  let db := (Functor.mapDerivedCategoryPlusCompIso J D).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso b ≪≫ Functor.mapDerivedCategoryPlusCompIso E J'
  let dc := (Functor.mapDerivedCategoryPlusCompIso C Q').symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso c ≪≫ Functor.mapDerivedCategoryPlusCompIso Q D
  let dd := (Functor.mapDerivedCategoryPlusCompIso A F').symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso d ≪≫ Functor.mapDerivedCategoryPlusCompIso F E
  let l : G.mapDerivedCategoryPlus ⋙ Q.mapDerivedCategoryPlus ⋙ D.mapDerivedCategoryPlus ⟶
      A.mapDerivedCategoryPlus ⋙ F'.mapDerivedCategoryPlus ⋙ J'.mapDerivedCategoryPlus :=
    Functor.whiskerRight de D.mapDerivedCategoryPlus ≫
      Functor.whiskerLeft F.mapDerivedCategoryPlus db.hom ≫
      Functor.whiskerRight dd.inv J'.mapDerivedCategoryPlus
  let t : G.mapDerivedCategoryPlus ⋙ Q.mapDerivedCategoryPlus ⋙ D.mapDerivedCategoryPlus ⟶
      A.mapDerivedCategoryPlus ⋙ F'.mapDerivedCategoryPlus ⋙ J'.mapDerivedCategoryPlus :=
    Functor.whiskerLeft G.mapDerivedCategoryPlus dc.inv ≫
      Functor.whiskerRight da.hom Q'.mapDerivedCategoryPlus ≫
      Functor.whiskerLeft A.mapDerivedCategoryPlus de'
  have ht : l = t := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso A₁)
    intro K
    simp only [l, t, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    have hd : dd.inv.app (DerivedCategory.Plus.Qh.obj K) ≫
        F'.mapDerivedCategoryPlus.map (A.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        F'.mapDerivedCategoryPlusFactorsh.hom.app (A.mapHomotopyCategoryPlus.obj K) =
      E.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        E.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus d.inv).app K) := by
      simpa only [dd, exactPlusNatIso_symm,
        Iso.symm_hom, Iso.symm_inv, Iso.trans_hom, Iso.trans_inv,
        NatTrans.comp_app, Category.assoc] using
        Functor.exactComparison_factorsh F E A F' d.symm K
    have hb := Functor.exactComparison_factorsh J D E J' b (F.mapHomotopyCategoryPlus.obj K)
    change db.hom.app _ ≫ _ = _ at hb
    have ha := Functor.exactComparison_factorsh G C A G' a K
    change da.hom.app _ ≫ _ = _ at ha
    have hc : dc.inv.app (DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj K)) ≫
        Q'.mapDerivedCategoryPlus.map (C.mapDerivedCategoryPlusFactorsh.hom.app
          (G.mapHomotopyCategoryPlus.obj K)) ≫
        Q'.mapDerivedCategoryPlusFactorsh.hom.app
          (C.mapHomotopyCategoryPlus.obj (G.mapHomotopyCategoryPlus.obj K)) =
      D.mapDerivedCategoryPlus.map (Q.mapDerivedCategoryPlusFactorsh.hom.app
          (G.mapHomotopyCategoryPlus.obj K)) ≫
        D.mapDerivedCategoryPlusFactorsh.hom.app
          (Q.mapHomotopyCategoryPlus.obj (G.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus c.inv).app
          (G.mapHomotopyCategoryPlus.obj K)) := by
      simpa only [dc, exactPlusNatIso_symm,
        Iso.symm_hom, Iso.symm_inv, Iso.trans_hom, Iso.trans_inv,
        NatTrans.comp_app, Category.assoc] using
        Functor.exactComparison_factorsh Q D C Q' c.symm (G.mapHomotopyCategoryPlus.obj K)
    have he := Etale.ClopenMateNormalization.clopenLocalizedSquarePlus_fac e K
    have he' := Etale.ClopenMateNormalization.clopenLocalizedSquarePlus_fac e'
      (A.mapHomotopyCategoryPlus.obj K)
    rw [← cancel_mono (J'.mapDerivedCategoryPlus.map
        (F'.mapDerivedCategoryPlus.map (A.mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
      J'.mapDerivedCategoryPlus.map (F'.mapDerivedCategoryPlusFactorsh.hom.app
        (A.mapHomotopyCategoryPlus.obj K)) ≫
      J'.mapDerivedCategoryPlusFactorsh.hom.app
        (F'.mapHomotopyCategoryPlus.obj (A.mapHomotopyCategoryPlus.obj K)))]
    simp only [Category.assoc]
    rw [← J'.mapDerivedCategoryPlus.map_comp_assoc,
      ← J'.mapDerivedCategoryPlus.map_comp_assoc]
    simp only [Category.assoc]
    rw [hd]
    simp only [Functor.map_comp, Category.assoc]
    have hdn := J'.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus d.inv).app K)
    simp only [Functor.comp_map] at hdn
    erw [hdn]
    have hbn := db.hom.naturality (F.mapDerivedCategoryPlusFactorsh.hom.app K)
    simp only [Functor.comp_map] at hbn
    erw [← reassoc_of% hbn, reassoc_of% hb]
    rw [← D.mapDerivedCategoryPlus.map_comp_assoc,
      ← D.mapDerivedCategoryPlus.map_comp_assoc]
    simp only [Category.assoc]
    erw [he]
    simp only [Functor.map_comp, Category.assoc]
    have hen := D.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus e).app K)
    simp only [Functor.comp_map] at hen
    erw [reassoc_of% hen]
    have he'n := de'.naturality (A.mapDerivedCategoryPlusFactorsh.hom.app K)
    simp only [Functor.comp_map] at he'n
    erw [← reassoc_of% he'n, he']
    conv_rhs =>
      rw [← Q'.mapDerivedCategoryPlus.map_comp_assoc,
        ← Q'.mapDerivedCategoryPlus.map_comp_assoc]
    simp only [Category.assoc]
    erw [ha]
    simp only [Functor.map_comp, Category.assoc]
    have han := Q'.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus a.hom).app K)
    simp only [Functor.comp_map] at han
    erw [reassoc_of% han]
    have hcn := dc.inv.naturality (G.mapDerivedCategoryPlusFactorsh.hom.app K)
    simp only [Functor.comp_map] at hcn
    erw [← reassoc_of% hcn, reassoc_of% hc]
    let l₀ : G ⋙ Q ⋙ D ⟶ A ⋙ F' ⋙ J' :=
      Functor.whiskerRight e D ≫ Functor.whiskerLeft F b.hom ≫
        Functor.whiskerRight d.inv J'
    let t₀ : G ⋙ Q ⋙ D ⟶ A ⋙ F' ⋙ J' :=
      Functor.whiskerLeft G c.inv ≫ Functor.whiskerRight a.hom Q' ≫
        Functor.whiskerLeft A e'
    have h₀ : l₀ = t₀ := by
      apply NatTrans.ext
      funext N
      exact h N
    have hh := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus h₀) K
    simp only [l₀, t₀, NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
      homotopyPlus_whiskerRight_app, homotopyPlus_whiskerLeft_app] at hh
    have hh' := congrArg
      (fun z ↦ D.mapDerivedCategoryPlus.map
          (Q.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
        D.mapDerivedCategoryPlus.map (Q.mapDerivedCategoryPlusFactorsh.hom.app
          (G.mapHomotopyCategoryPlus.obj K)) ≫
        D.mapDerivedCategoryPlusFactorsh.hom.app
          (Q.mapHomotopyCategoryPlus.obj (G.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map z) hh
    simp only [Functor.map_comp] at hh'
    convert hh' using 1 <;> rfl
  exact congr_app ht M

private theorem coefficientClopenAlphaPlus
    (B Λ : Type (u + 1)) [CommRing B] [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (H B W Λ φ).mapDerivedCategoryPlus.map
        ((Etale.ClopenMateNormalization.derivedAlphaPlus Λ k r p i h).app M) ≫
      (hOpenPlus B Λ φ k).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus.obj M) ≫
      (moduleJ B k).mapDerivedCategoryPlus.map ((hPullbackPlus B Λ φ r).inv.app M) =
    (hPullbackPlus B Λ φ p).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj M) ≫
      (modulePullback B p).mapDerivedCategoryPlus.map ((hOpenPlus B Λ φ i).hom.app M) ≫
      (Etale.ClopenMateNormalization.clopenLocalizedSquarePlus
        (singleAlpha B k r p i h)).app ((H B S Λ φ).mapDerivedCategoryPlus.obj M) := by
  exact exactAlphaCube
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) r)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) p)
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (moduleJ B i) (modulePullback B r) (modulePullback B p) (moduleJ B k)
    (H B S Λ φ) (H B T Λ φ) (H B V Λ φ) (H B W Λ φ)
    (Etale.ClopenMateNormalization.alpha Λ k r p i h) (singleAlpha B k r p i h)
    (@asIso _ _ _ _ (hOpen B i Λ φ) (hOpen_isIso B i Λ φ))
    (@asIso _ _ _ _ (hOpen B k Λ φ) (hOpen_isIso B k Λ φ))
    (hPullbackIso B Λ φ p) (hPullbackIso B Λ φ r)
    (finiteCoefficientClopenAlpha B Λ φ k r p i h) M

private theorem coefficientPlusCounit
    (B Λ : Type (u + 1)) [CommRing B] [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (hPullbackPlus B Λ φ f).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K) ≫
      (modulePullback B f).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange (hDirect B f Λ φ)).app K) ≫
      (clopenModuleAdj B f).derivedPlus.counit.app
        ((H B X Λ φ).mapDerivedCategoryPlus.obj K) =
    (H B X Λ φ).mapDerivedCategoryPlus.map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus.counit.app K) := by
  let a := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  let b := clopenModuleAdj B f
  let e := @asIso _ _ _ _ (hPullbackInv B f Λ φ) (hPullbackInv_isIso B f Λ φ)
  have hm : (mateEquiv a b e.hom) = hDirect B f Λ φ := by
    exact ((mateEquiv a b).apply_symm_apply _)
  rw [← hm, Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv a b e]
  change (hPullbackPlus B Λ φ f).inv.app _ ≫
    (modulePullback B f).mapDerivedCategoryPlus.map
      ((mateEquiv a.derivedPlus b.derivedPlus
        (hPullbackPlus B Λ φ f).hom).app K) ≫ _ = _
  rw [mateEquiv_counit]
  exact Iso.inv_hom_id_app_assoc (hPullbackPlus B Λ φ f) _ _

/-- The canonical coefficient realization transports the normalized finite etale mate.
Source: Stacks Project, Tags 03DA, 07A7, 099R and 09AF; the coefficient-realization
part of steps 4--5 of the parent calculus proof
(blueprint: lem-cbc-single-level-finite-proper-open-transport).
Proof: factor H as site inverse image, finite-coefficient realization, and restriction
of scalars. The underlying-sheaf identification of C fixes every sheafification-unit
section. Its direct-image comparison is cDirect, and the inverse-image comparison is
its adjunction mate. The open comparison is the mate for extension by zero. On the
clopen lift all three comparisons preserve the projection onto the first factor of
the disjoint-cover product, since they preserve restriction and zero sections.
They consequently preserve the ordinary alpha, with its inverse cartesian comparison
and its two compositors. Apply exact localization to this equality. The unit-normalized
derived direct-image comparison is hR, including the bounded-below inclusion into the
unbounded category. Transposing alpha under the two proper adjunctions gives the
singleDerivedGamma square. The finite site-transport theorem identifies its fixed-ring
site part with the etale derived mate; etale clopen normalization identifies this with
the specified normalizedComparison. Composition of the coefficient and site squares
is exactly the displayed equation. No flatness of the scalar map is required. -/
theorem singleLevelFiniteProperOpenTransport
    (B Λ : Type (u + 1)) [CommRing B] [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (hJ B i Λ φ).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj L) ≫
      (moduleJ B i).mapDerivedCategory.map ((hR B r Λ φ).app L) ≫
      (MateEvaluationScalars.singleDerivedGamma B k r p i h).app
        ((HD B V Λ φ).obj L) =
    (HD B T Λ φ).map
        ((Etale.ClopenMateNormalization.normalizedComparison Λ k r p i h).hom.app L) ≫
      (hR B p Λ φ).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj L) ≫
      (moduleDirectImage B p).rightDerivedFunctor.map ((hJ B k Λ φ).hom.app L) := by
  let a := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r
  let b := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  let a' := clopenModuleAdj B r
  let b' := clopenModuleAdj B p
  let γ := (mateEquiv a'.derivedPlus b'.derivedPlus
    (Etale.ClopenMateNormalization.clopenLocalizedSquarePlus
      (singleAlpha B k r p i h)))
  have heq := transport_mate a.derivedPlus b.derivedPlus a'.derivedPlus b'.derivedPlus
    (H B S Λ φ).mapDerivedCategoryPlus (H B V Λ φ).mapDerivedCategoryPlus
    (H B T Λ φ).mapDerivedCategoryPlus (H B W Λ φ).mapDerivedCategoryPlus
    (hPullbackPlus B Λ φ r).symm (hPullbackPlus B Λ φ p).symm
    (Functor.rightDerivedFunctorPlusBaseChange (hDirect B r Λ φ))
    (Functor.rightDerivedFunctorPlusBaseChange (hDirect B p Λ φ))
    (hOpenPlus B Λ φ i) (hOpenPlus B Λ φ k)
    (Etale.ClopenMateNormalization.derivedAlphaPlus Λ k r p i h)
    (Etale.ClopenMateNormalization.clopenLocalizedSquarePlus
      (singleAlpha B k r p i h))
    (coefficientPlusCounit B Λ φ r) (coefficientPlusCounit B Λ φ p)
    (coefficientClopenAlphaPlus B Λ φ k r p i h) L
  have hn := congr_app
    (Etale.ClopenMateNormalization.etaleClopenMateNormalization Λ k r p i h).2.1 L
  change (hOpenPlus B Λ φ i).hom.app _ ≫ _ ≫
      γ.app ((H B V Λ φ).mapDerivedCategoryPlus.obj L) = _ at heq
  change _ = (H B T Λ φ).mapDerivedCategoryPlus.map
      ((Etale.ClopenMateNormalization.derivedMatePlus Λ k r p i h).app L) ≫ _ at heq
  rw [hn] at heq
  have ham := Etale.ClopenMateNormalization.mate_ambient a' b'
    (TwoSquare.mk _ _ _ _ (singleAlpha B k r p i h))
    ((H B V Λ φ).mapDerivedCategoryPlus.obj L)
  simp only [Etale.ClopenMateNormalization.clopenLocalizedSquare] at ham
  change DerivedCategory.Plus.ι.map (γ.app _) ≫ _ =
    (moduleJ B i).mapDerivedCategory.map _ ≫
      (MateEvaluationScalars.singleDerivedGamma B k r p i h).app _ at ham
  have ht := congrArg (fun z ↦ DerivedCategory.Plus.ι.map z ≫
    (moduleDirectImage B p).rightDerivedFunctorPlusCompatibility.hom.app
      ((moduleJ B k).mapDerivedCategoryPlus.obj
        ((H B V Λ φ).mapDerivedCategoryPlus.obj L))) heq
  simp only [Functor.map_comp, Category.assoc] at ht
  rw [ham] at ht
  have hnat := (moduleDirectImage B p).rightDerivedFunctorPlusCompatibility.hom.naturality
    ((hOpenPlus B Λ φ k).hom.app L)
  simp only [Functor.comp_map] at hnat
  erw [hnat] at ht
  simpa only [hJ, hR, hOpenPlus, HD, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Functor.map_id, Functor.map_comp,
    Functor.comp_obj, Etale.rightDerivedLowerStarPlus,
    MateEvaluationScalars.j, MateEvaluationScalars.r, exactPlusMap_ι, Category.assoc] using ht

end AlgebraicGeometry.ProEtale.StrictTower
