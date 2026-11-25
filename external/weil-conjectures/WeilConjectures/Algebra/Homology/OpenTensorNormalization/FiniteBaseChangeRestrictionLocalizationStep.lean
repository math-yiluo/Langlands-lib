/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteBaseChangeRestrictionOrdinaryPinMate

/-! Localization of the finite restriction representative.
(blueprint: lem-sf-finite-base-change-restriction-localization-step)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

private theorem comparison_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    {P T : CochainComplex C ℤ} (f : P ⟶ T) :
    L.map (DerivedCategory.Q.map f) ≫ derivedPullbackComplexComparison F L ε T =
      derivedPullbackComplexComparison F L ε P ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let a : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv L ≫
      Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) ε ≫
      Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso D).hom
  simpa only [a, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, derivedPullbackComplexComparison] using
      a.naturality f

private def complexComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := derivedPullbackComplexComparison F L ε P
  naturality _ _ f := comparison_naturality F L ε f

private theorem invert_square
    {K : Type*} [Category K] {A B C D E F : K}
    (θ : A ≅ B) (l : B ⟶ C) (m : C ⟶ D) (p : A ⟶ E) (q : E ⟶ F)
    (v : F ≅ D) (h : θ.hom ≫ l ≫ m = p ≫ q ≫ v.hom) :
    θ.inv ≫ p ≫ q = (l ≫ m) ≫ v.inv := by
  apply (Iso.inv_comp_eq θ).2
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv v).2
  exact (Category.assoc _ _ _).trans h.symm

private theorem paste_left
    {C : Type*} [Category C]
    {S A B D E F Z N M O A₂ A₃ S₂ S₃ O₂ O₃ : C}
    (a : S ⟶ A) (b : A ⟶ B) (t : B ⟶ D) (u : D ⟶ E)
    (v : E ⟶ F) (w : F ⟶ Z) (p : B ⟶ N) (q : N ⟶ E)
    (l : N ⟶ M) (m : M ⟶ O) (n : O ⟶ Z)
    (h : A ⟶ A₂) (k : A₂ ⟶ A₃) (z : A₃ ⟶ M)
    (x : S ⟶ S₂) (a' : S₂ ⟶ A₂) (m' : A₃ ⟶ O₂) (z' : O₂ ⟶ O)
    (y : S₂ ⟶ S₃) (e : S₃ ⟶ O₃) (c : O₃ ⟶ O₂)
    (ht : t ≫ u = p ≫ q) (hq : q ≫ v ≫ w = l ≫ m ≫ n)
    (hb : b ≫ p ≫ l = h ≫ k ≫ z) (ha : a ≫ h = x ≫ a')
    (hz : z ≫ m = m' ≫ z') (hm : a' ≫ k ≫ m' = y ≫ e ≫ c) :
    a ≫ b ≫ t ≫ u ≫ v ≫ w = x ≫ y ≫ e ≫ c ≫ z' ≫ n := by
  rw [reassoc_of% ht, hq]
  rw [reassoc_of% hb, reassoc_of% ha, reassoc_of% hz, reassoc_of% hm]

private theorem paste_right
    {C : Type*} [Category C]
    {S A B D E F Z V W N M L K O R : C}
    (s : S ⟶ A) (r : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E) (c : E ⟶ F)
    (w : F ⟶ Z) (g : B ⟶ V) (h : V ⟶ W) (i : W ⟶ F)
    (j : A ⟶ N) (r' : N ⟶ V) (v : W ⟶ M) (i' : M ⟶ Z)
    (k : N ⟶ L) (e : L ⟶ K) (d : K ⟶ M)
    (x : S ⟶ O) (y : O ⟶ R) (z : R ⟶ L) (f : R ⟶ K)
    (hg : a ≫ b ≫ c = g ≫ h ≫ i)
    (hr : r ≫ g = j ≫ r') (hi : i ≫ w = v ≫ i')
    (ho : r' ≫ h ≫ v = k ≫ e ≫ d)
    (hs : s ≫ j ≫ k = x ≫ y ≫ z)
    (he : z ≫ e = f) :
    s ≫ r ≫ a ≫ b ≫ c ≫ w = x ≫ y ≫ f ≫ d ≫ i' := by
  rw [reassoc_of% hg, reassoc_of% hr, hi, reassoc_of% ho]
  rw [reassoc_of% hs, reassoc_of% he]

private theorem exact_square_model
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    (F : C ⥤ D) (V : D ⥤ E) (G : C ⥤ B) (H : B ⥤ E)
    [F.Additive] [V.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : F ⋙ V ≅ G ⋙ H) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategorySquareIso c).hom.app (DerivedCategory.Q.obj P) ≫
      H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
    V.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P) := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F V P]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem categorical_localization_square
    {C D B E C₀ D₀ B₀ E₀ T V W Z T₀ V₀ W₀ Z₀ : Type*}
    [Category C] [Category D] [Category B] [Category E]
    [Category C₀] [Category D₀] [Category B₀] [Category E₀]
    [Category T] [Category V] [Category W] [Category Z]
    [Category T₀] [Category V₀] [Category W₀] [Category Z₀]
    (Fc : C ⥤ D) (Hc : D ⥤ E) (Gc : C ⥤ B) (Jc : B ⥤ E)
    (Xc : C ⥤ C₀) (Uc : D ⥤ D₀) (X'c : B ⥤ B₀) (U'c : E ⥤ E₀)
    (Ic : C₀ ⥤ D₀) (I'c : B₀ ⥤ E₀) (gc : C₀ ⥤ B₀) (hc : D₀ ⥤ E₀)
    (Qx : C ⥤ T) (Qu : D ⥤ V) (Qx' : B ⥤ W) (Qu' : E ⥤ Z)
    (qx : C₀ ⥤ T₀) (qu : D₀ ⥤ V₀) (qx' : B₀ ⥤ W₀) (qu' : E₀ ⥤ Z₀)
    (Fd : T ⥤ V) (Hd : V ⥤ Z) (Gd : T ⥤ W) (Jd : W ⥤ Z)
    (Xd : T ⥤ T₀) (Ud : V ⥤ V₀) (X'd : W ⥤ W₀) (U'd : Z ⥤ Z₀)
    (Id : T₀ ⥤ V₀) (I'd : W₀ ⥤ Z₀) (Lg : T₀ ⥤ W₀) (Lh : V₀ ⥤ Z₀)
    (φF : Qx ⋙ Fd ≅ Fc ⋙ Qu) (φH : Qu ⋙ Hd ≅ Hc ⋙ Qu')
    (φG : Qx ⋙ Gd ≅ Gc ⋙ Qx') (φJ : Qx' ⋙ Jd ≅ Jc ⋙ Qu')
    (φX : Qx ⋙ Xd ≅ Xc ⋙ qx) (φU : Qu ⋙ Ud ≅ Uc ⋙ qu)
    (φX' : Qx' ⋙ X'd ≅ X'c ⋙ qx') (φU' : Qu' ⋙ U'd ≅ U'c ⋙ qu')
    (φI : qx ⋙ Id ≅ Ic ⋙ qu) (φI' : qx' ⋙ I'd ≅ I'c ⋙ qu')
    (aG : qx ⋙ Lg ⟶ gc ⋙ qx') (aH : qu ⋙ Lh ⟶ hc ⋙ qu')
    (δG : Gd ⋙ X'd ≅ Xd ⋙ Lg) (δH : Hd ⋙ U'd ≅ Ud ⋙ Lh)
    (r : Fd ⋙ Ud ≅ Xd ⋙ Id) (r' : Jd ⋙ U'd ≅ X'd ⋙ I'd)
    (θ : Lg ⋙ I'd ≅ Id ⋙ Lh) (sD : Fd ⋙ Hd ≅ Gd ⋙ Jd) (P : C)
    (sC : Hc.obj (Fc.obj P) ⟶ Jc.obj (Gc.obj P))
    (cG : X'c.obj (Gc.obj P) ⟶ gc.obj (Xc.obj P))
    (cU : U'c.obj (Hc.obj (Fc.obj P)) ⟶ hc.obj (Uc.obj (Fc.obj P)))
    (rC : Uc.obj (Fc.obj P) ⟶ Ic.obj (Xc.obj P))
    (r'C : U'c.obj (Jc.obj (Gc.obj P)) ⟶ I'c.obj (X'c.obj (Gc.obj P)))
    (v : I'c.obj (gc.obj (Xc.obj P)) ≅ hc.obj (Ic.obj (Xc.obj P)))
    (hS : sD.hom.app (Qx.obj P) ≫ Jd.map (φG.hom.app P) ≫ φJ.hom.app (Gc.obj P) =
      Hd.map (φF.hom.app P) ≫ φH.hom.app (Fc.obj P) ≫ Qu'.map sC)
    (hComplex : cU ≫ hc.map rC ≫ v.inv = U'c.map sC ≫ r'C ≫ I'c.map cG)
    (hTheta : θ.hom.app (qx.obj (Xc.obj P)) ≫
      Lh.map (φI.hom.app (Xc.obj P)) ≫ aH.app (Ic.obj (Xc.obj P)) =
      I'd.map (aG.app (Xc.obj P)) ≫ φI'.hom.app (gc.obj (Xc.obj P)) ≫ qu'.map v.hom)
    (hO : r.hom.app (Qx.obj P) ≫ Id.map (φX.hom.app P) ≫ φI.hom.app (Xc.obj P) =
      Ud.map (φF.hom.app P) ≫ φU.hom.app (Fc.obj P) ≫ qu.map rC)
    (hU : δH.hom.app (Qu.obj (Fc.obj P)) ≫ Lh.map (φU.hom.app (Fc.obj P)) ≫
      aH.app (Uc.obj (Fc.obj P)) =
      U'd.map (φH.hom.app (Fc.obj P)) ≫ φU'.hom.app (Hc.obj (Fc.obj P)) ≫ qu'.map cU)
    (hG : δG.hom.app (Qx.obj P) ≫ Lg.map (φX.hom.app P) ≫ aG.app (Xc.obj P) =
      X'd.map (φG.hom.app P) ≫ φX'.hom.app (Gc.obj P) ≫ qx'.map cG)
    (hO' : r'.hom.app (Qx'.obj (Gc.obj P)) ≫ I'd.map (φX'.hom.app (Gc.obj P)) ≫
      φI'.hom.app (X'c.obj (Gc.obj P)) =
      U'd.map (φJ.hom.app (Gc.obj P)) ≫ φU'.hom.app (Jc.obj (Gc.obj P)) ≫ qu'.map r'C) :
    let M := Qx.obj P
    let B := Lg.map (φX.hom.app P) ≫ aG.app (Xc.obj P)
    (δH.hom.app (Fd.obj M) ≫ Lh.map (r.hom.app M) ≫ θ.inv.app (Xd.obj M)) ≫ I'd.map B =
    (U'd.map (sD.hom.app M) ≫ r'.hom.app (Gd.obj M) ≫ I'd.map (δG.hom.app M)) ≫
      I'd.map B := by
  let P₀ := Xc.obj P
  let fX := φX.hom.app P
  let θC := v.inv
  let C := U'd.map
      (Hd.map (φF.hom.app P)) ≫
    U'd.map (φH.hom.app (Fc.obj P)) ≫
    φU'.hom.app (Hc.obj (Fc.obj P))
  have hC : cU ≫ hc.map rC ≫ θC =
      (U'c).map sC ≫ r'C ≫ I'c.map cG := hComplex
  have hθ : θ.inv.app (qx.obj P₀) ≫
      I'd.map (aG.app P₀) ≫
      φI'.hom.app (gc.obj P₀) =
    (Lh.map (φI.hom.app P₀) ≫
      aH.app (Ic.obj P₀)) ≫ qu'.map θC := by
    exact invert_square (θ.app (qx.obj P₀))
      (Lh.map (φI.hom.app P₀))
      (aH.app (Ic.obj P₀)) (I'd.map (aG.app P₀))
      (φI'.hom.app (gc.obj P₀)) (qu'.mapIso v) hTheta
  have hnθ : Lh.map (Id.map fX) ≫
      θ.inv.app (qx.obj P₀) =
    θ.inv.app (Xd.obj (Qx.obj P)) ≫
      I'd.map (Lg.map fX) := θ.inv.naturality fX
  have hnU : U'd.map
      (Hd.map (φF.hom.app P)) ≫
      δH.hom.app (Qu.obj (Fc.obj P)) =
    δH.hom.app (Fd.obj (Qx.obj P)) ≫
      Lh.map (Ud.map
        (φF.hom.app P)) :=
    δH.hom.naturality (φF.hom.app P)
  have hnH : Lh.map (qu.map rC) ≫ aH.app (Ic.obj P₀) =
      aH.app (Uc.obj (Fc.obj P)) ≫ qu'.map (hc.map rC) :=
    aH.naturality rC
  have hnO' : U'd.map
      (Jd.map (φG.hom.app P)) ≫
      r'.hom.app (Qx'.obj (Gc.obj P)) =
    r'.hom.app (Gd.obj (Qx.obj P)) ≫
      I'd.map (X'd.map
        (φG.hom.app P)) :=
    r'.hom.naturality (φG.hom.app P)
  have hnI' : I'd.map (qx'.map cG) ≫
      φI'.hom.app (gc.obj P₀) =
    φI'.hom.app
        ((X'c).obj (Gc.obj P)) ≫
      qu'.map (I'c.map cG) := φI'.hom.naturality cG
  have hnE : U'd.map (Qu'.map sC) ≫
      φU'.hom.app (Jc.obj (Gc.obj P)) =
    φU'.hom.app (Hc.obj (Fc.obj P)) ≫
      qu'.map ((U'c).map sC) :=
    φU'.hom.naturality sC
  dsimp only
  apply (cancel_mono (φI'.hom.app (gc.obj P₀))).1
  simp only [Category.assoc]
  change
    δH.hom.app (Fd.obj (Qx.obj P)) ≫
      Lh.map (r.hom.app (Qx.obj P)) ≫
      θ.inv.app (Xd.obj (Qx.obj P)) ≫
      I'd.map (Lg.map fX ≫ aG.app P₀) ≫
      φI'.hom.app (gc.obj P₀) =
    U'd.map
      (sD.hom.app (Qx.obj P)) ≫
      r'.hom.app (Gd.obj (Qx.obj P)) ≫
      I'd.map (δG.hom.app (Qx.obj P)) ≫
      I'd.map (Lg.map fX ≫ aG.app P₀) ≫
      φI'.hom.app (gc.obj P₀)
  simp only [Functor.map_comp, Category.assoc]
  trans C ≫ qu'.map (cU ≫ hc.map rC ≫ θC)
  · have hp := paste_left
      (δH.hom.app (Fd.obj (Qx.obj P)))
      (Lh.map (r.hom.app (Qx.obj P)))
      (θ.inv.app (Xd.obj (Qx.obj P)))
      (I'd.map (Lg.map fX))
      (I'd.map (aG.app P₀))
      (φI'.hom.app (gc.obj P₀))
      (Lh.map (Id.map fX))
      (θ.inv.app (qx.obj P₀))
      (Lh.map (φI.hom.app P₀))
      (aH.app (Ic.obj P₀)) (qu'.map θC)
      (Lh.map (Ud.map
        (φF.hom.app P)))
      (Lh.map (φU.hom.app (Fc.obj P)))
      (Lh.map (qu.map rC))
      (U'd.map
        (Hd.map (φF.hom.app P)))
      (δH.hom.app (Qu.obj (Fc.obj P)))
      (aH.app (Uc.obj (Fc.obj P))) (qu'.map (hc.map rC))
      (U'd.map (φH.hom.app (Fc.obj P)))
      (φU'.hom.app (Hc.obj (Fc.obj P)))
      (qu'.map cU) hnθ.symm
      (by simpa only [Category.assoc] using hθ)
      (by simpa only [Functor.map_comp] using congrArg Lh.map hO)
      hnU.symm hnH hU
    simpa only [C, Functor.map_comp, Category.assoc] using hp
  · rw [hC]
    symm
    have hp := paste_right
      (U'd.map
        (sD.hom.app (Qx.obj P)))
      (r'.hom.app (Gd.obj (Qx.obj P)))
      (I'd.map (δG.hom.app (Qx.obj P)))
      (I'd.map (Lg.map fX))
      (I'd.map (aG.app P₀))
      (φI'.hom.app (gc.obj P₀))
      (I'd.map (X'd.map
        (φG.hom.app P)))
      (I'd.map (φX'.hom.app (Gc.obj P)))
      (I'd.map (qx'.map cG))
      (U'd.map
        (Jd.map (φG.hom.app P)))
      (r'.hom.app (Qx'.obj (Gc.obj P)))
      (φI'.hom.app
        ((X'c).obj (Gc.obj P)))
      (qu'.map (I'c.map cG))
      (U'd.map (φJ.hom.app (Gc.obj P)))
      (φU'.hom.app (Jc.obj (Gc.obj P)))
      (qu'.map r'C)
      (U'd.map
        (Hd.map (φF.hom.app P)))
      (U'd.map (φH.hom.app (Fc.obj P)))
      (U'd.map (Qu'.map sC))
      (φU'.hom.app (Hc.obj (Fc.obj P)) ≫
        qu'.map ((U'c).map sC))
      (by simpa only [Functor.map_comp] using congrArg I'd.map hG)
      hnO'.symm hnI' hO'
      (by simpa only [Functor.map_comp] using congrArg U'd.map hS) hnE
    simpa only [C, Functor.map_comp, Category.assoc] using hp

private theorem localization_of_models
    {C D B E C₀ D₀ B₀ E₀ : Type*}
    [Category C] [Category D] [Category B] [Category E]
    [Category C₀] [Category D₀] [Category B₀] [Category E₀]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [Abelian C₀] [Abelian D₀] [Abelian B₀] [Abelian E₀]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [HasDerivedCategory C₀] [HasDerivedCategory D₀]
    [HasDerivedCategory B₀] [HasDerivedCategory E₀]
    (F : C ⥤ D) (H : D ⥤ E) (G : C ⥤ B) (J : B ⥤ E)
    (EX : C ⥤ C₀) (EU : D ⥤ D₀) (EX' : B ⥤ B₀) (EU' : E ⥤ E₀)
    (I : C₀ ⥤ D₀) (I' : B₀ ⥤ E₀)
    [F.Additive] [H.Additive] [G.Additive] [J.Additive]
    [EX.Additive] [EU.Additive] [EX'.Additive] [EU'.Additive]
    [I.Additive] [I'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits EX] [PreservesFiniteColimits EX]
    [PreservesFiniteLimits EU] [PreservesFiniteColimits EU]
    [PreservesFiniteLimits EX'] [PreservesFiniteColimits EX']
    [PreservesFiniteLimits EU'] [PreservesFiniteColimits EU']
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
    (Lg : DerivedCategory C₀ ⥤ DerivedCategory B₀)
    (Lh : DerivedCategory D₀ ⥤ DerivedCategory E₀)
    (g : C₀ ⥤ B₀) (h : D₀ ⥤ E₀) [g.Additive] [h.Additive]
    (aG : DerivedCategory.Q ⋙ Lg ⟶
      g.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (aH : DerivedCategory.Q ⋙ Lh ⟶
      h.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δG : G.mapDerivedCategory ⋙ EX'.mapDerivedCategory ≅ EX.mapDerivedCategory ⋙ Lg)
    (δH : H.mapDerivedCategory ⋙ EU'.mapDerivedCategory ≅ EU.mapDerivedCategory ⋙ Lh)
    (r : F.mapDerivedCategory ⋙ EU.mapDerivedCategory ≅
      EX.mapDerivedCategory ⋙ I.mapDerivedCategory)
    (r' : J.mapDerivedCategory ⋙ EU'.mapDerivedCategory ≅
      EX'.mapDerivedCategory ⋙ I'.mapDerivedCategory)
    (θ : Lg ⋙ I'.mapDerivedCategory ≅ I.mapDerivedCategory ⋙ Lh)
    (s : F ⋙ H ≅ G ⋙ J) (P : CochainComplex C ℤ)
    (pG : G ⋙ EX' ≅ EX ⋙ g) (pU : H ⋙ EU' ≅ EU ⋙ h)
    (pO : F ⋙ EU ≅ EX ⋙ I) (pO' : J ⋙ EU' ≅ EX' ⋙ I')
    (pθ : g ⋙ I' ≅ I ⋙ h)
    (hOrd : ∀ N : C,
      pU.hom.app (F.obj N) ≫ h.map (pO.hom.app N) ≫
        pθ.inv.app (EX.obj N) =
      EU'.map (s.hom.app N) ≫ pO'.hom.app (G.obj N) ≫
        I'.map (pG.hom.app N))
    (hTheta : θ.hom.app (DerivedCategory.Q.obj
        ((EX.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      Lh.map (I.mapDerivedCategoryFactors.hom.app
        ((EX.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      aH.app ((I.mapHomologicalComplex (.up ℤ)).obj
        ((EX.mapHomologicalComplex (.up ℤ)).obj P)) =
      I'.mapDerivedCategory.map (aG.app ((EX.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      I'.mapDerivedCategoryFactors.hom.app
        ((g.mapHomologicalComplex (.up ℤ)).obj
          ((EX.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex pθ (.up ℤ)).app
        ((EX.mapHomologicalComplex (.up ℤ)).obj P)).hom)
    (hO : r.hom.app (DerivedCategory.Q.obj P) ≫
      I.mapDerivedCategory.map (EX.mapDerivedCategoryFactors.hom.app P) ≫
      I.mapDerivedCategoryFactors.hom.app ((EX.mapHomologicalComplex (.up ℤ)).obj P) =
      EU.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      EU.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex pO.hom (.up ℤ)).app P))
    (hU : δH.hom.app (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      Lh.map (EU.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      aH.app ((EU.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
      EU'.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      EU'.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex pU.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    (hG : δG.hom.app (DerivedCategory.Q.obj P) ≫
      Lg.map (EX.mapDerivedCategoryFactors.hom.app P) ≫
      aG.app ((EX.mapHomologicalComplex (.up ℤ)).obj P) =
      EX'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
      EX'.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex pG.hom (.up ℤ)).app P))
    (hO' : r'.hom.app (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      I'.mapDerivedCategory.map (EX'.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      I'.mapDerivedCategoryFactors.hom.app ((EX'.mapHomologicalComplex (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) =
      EU'.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      EU'.mapDerivedCategoryFactors.hom.app ((J.mapHomologicalComplex (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex pO'.hom (.up ℤ)).app
        ((G.mapHomologicalComplex (.up ℤ)).obj P))) :
    let M := DerivedCategory.Q.obj P
    let B := Lg.map (EX.mapDerivedCategoryFactors.hom.app P) ≫
      aG.app ((EX.mapHomologicalComplex (.up ℤ)).obj P)
    (δH.hom.app (F.mapDerivedCategory.obj M) ≫
      Lh.map (r.hom.app M) ≫ θ.inv.app (EX.mapDerivedCategory.obj M)) ≫
      I'.mapDerivedCategory.map B =
    (EU'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso s).hom.app M) ≫
      r'.hom.app (G.mapDerivedCategory.obj M) ≫ I'.mapDerivedCategory.map (δG.hom.app M)) ≫
      I'.mapDerivedCategory.map B := by
  refine categorical_localization_square
    (F.mapHomologicalComplex (.up ℤ)) (H.mapHomologicalComplex (.up ℤ))
    (G.mapHomologicalComplex (.up ℤ)) (J.mapHomologicalComplex (.up ℤ))
    (EX.mapHomologicalComplex (.up ℤ)) (EU.mapHomologicalComplex (.up ℤ))
    (EX'.mapHomologicalComplex (.up ℤ)) (EU'.mapHomologicalComplex (.up ℤ))
    (I.mapHomologicalComplex (.up ℤ)) (I'.mapHomologicalComplex (.up ℤ))
    (g.mapHomologicalComplex (.up ℤ)) (h.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.Q (C := C)) (DerivedCategory.Q (C := D))
    (DerivedCategory.Q (C := B)) (DerivedCategory.Q (C := E))
    (DerivedCategory.Q (C := C₀)) (DerivedCategory.Q (C := D₀))
    (DerivedCategory.Q (C := B₀)) (DerivedCategory.Q (C := E₀))
    F.mapDerivedCategory H.mapDerivedCategory G.mapDerivedCategory J.mapDerivedCategory
    EX.mapDerivedCategory EU.mapDerivedCategory EX'.mapDerivedCategory EU'.mapDerivedCategory
    I.mapDerivedCategory I'.mapDerivedCategory Lg Lh
    F.mapDerivedCategoryFactors H.mapDerivedCategoryFactors
    G.mapDerivedCategoryFactors J.mapDerivedCategoryFactors
    EX.mapDerivedCategoryFactors EU.mapDerivedCategoryFactors
    EX'.mapDerivedCategoryFactors EU'.mapDerivedCategoryFactors
    I.mapDerivedCategoryFactors I'.mapDerivedCategoryFactors
    aG aH δG δH r r' θ (Functor.mapDerivedCategorySquareIso s) P
    ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app P)
    ((NatTrans.mapHomologicalComplex pG.hom (.up ℤ)).app P)
    ((NatTrans.mapHomologicalComplex pU.hom (.up ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P))
    ((NatTrans.mapHomologicalComplex pO.hom (.up ℤ)).app P)
    ((NatTrans.mapHomologicalComplex pO'.hom (.up ℤ)).app
      ((G.mapHomologicalComplex (.up ℤ)).obj P))
    ((NatIso.mapHomologicalComplex pθ (.up ℤ)).app
      ((EX.mapHomologicalComplex (.up ℤ)).obj P)) ?_ ?_ hTheta hO hU hG hO'
  · exact exact_square_model F H G J s P
  · apply HomologicalComplex.Hom.ext
    funext n
    exact hOrd (P.X n)

/-- Localize the ordinary θ₀/pin/mate identity to the derived representative.

Source: the localization and model-equation part of
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md`.
Proof: expand the two finite pull pins and the two finite open pins on `P` and on
its fixed-scalar pullback along `g`. Use naturality of the realization factors to
transport the complex pin identity through the three square compositors. Finally
apply `Operations.theta_model` to the resolving complex. In detail, map the
ordinary square degreewise to complexes, then through `DerivedCategory.Q`.
Use the two pull pin model equations and the restriction parts of the two open
pin model equations. Naturality moves the realization factor through the
localized ordinary square. The exact-functor compositor factorization identifies
the localized fixed-scalar square with the three derived compositors. The
conclusion is the resulting identity after postcomposition with the model map;
its invertibility and cancellation are proved by the caller.
First apply complex-morphism extensionality to `hOrd` in every degree, using
the definition of `NatTrans.mapHomologicalComplex`. This gives equality of the
complete two pin-square cochain maps. More explicitly, write `F_j,F_h` for the
ordinary finite pullbacks along `j,gU`,
`E` for the U'-realization, `φ` for exact localization factors, and `a` for the
pullback complex comparison. Append the invertible factor `φ_{I'}(G(P₀))` to
both sides of the conclusion, where `P₀` is the X-realization of `P`. Naturality
of `theta.inv` at `φ_{E_X}(P)` and the inverse form of `theta_model P₀ hP`
replace the left theta tail by `D(H)(φ_I(P₀))`, then `a_H(I(P₀))`, then
`Q(θ₀⁻¹(P₀))`. The open-pin model at `P`, the pullU-pin model at `F_j(P)`,
and naturality of `a_H` then turn the entire left route into `C ≫ Q(α_P)`,
where `α_P` is the complex map whose components are the left side of `hOrd`, and
`C = D(E)(D(F_h)(φ_{F_j}(P)) ≫ φ_{F_h}(F_j(P))) ≫ φ_E(F_h(F_j(P)))`.
For the right route, the pull-pin model at `P` followed by factor naturality
moves `I'` through its ordinary comparison; the open'-pin model at `F_g(P)`
then leaves the exact square compositor. Expand its definition and use
`mapDerivedCategoryNatIso_fac` and
`mapDerivedCategoryCompIso_hom_app_factors` on its two routes. They give the
same prefix `C` followed by `Q(β_P)`, where `β_P` is the right complex map
in the degreewise hypothesis. Applying `Q.map` to the cochain equality equates
these tails. Finally cancel
only the appended exact restriction factor. No flatness cancellation of `B`
is performed in this lemma.
(blueprint: lem-sf-finite-base-change-restriction-localization-step) -/
theorem finite_base_change_restriction_localization_step
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)
    (P : CochainComplex (FiniteModules A X) ℤ)
    (hP : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hOrd : ∀ n : ℤ,
      e.pullU_pin.ordinary.hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj (P.X n)) ≫
        o.gUPull.ordinary.map (e.open_pin.star.hom.app (P.X n)) ≫
        o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj (P.X n)) =
      e.realizeU'.equivalence.functor.map
          ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom.app (P.X n)) ≫
        e.open'_pin.star.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj (P.X n)) ≫
        (restrict .ordinary j' (finiteInput A gU j' j g sq).S).map
          (e.pull_pin.ordinary.hom.app (P.X n))) :
    let r := Functor.isoWhiskerRight
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
      e.realizeU.derived ≪≫ e.openPull
    let M := DerivedCategory.Q.obj P
    let B := o.gPull.derived.map
      (e.realizeX.equivalence.functor.mapDerivedCategoryFactors.hom.app P) ≫
      derivedPullbackComplexComparison o.gPull.ordinary o.gPull.derived
        o.gPull.epsilon ((finiteComplexRealization e.realizeX).obj P)
    (e.pullU.hom.app ((finitePull A j).obj M) ≫
        o.gUPull.derived.map (r.hom.app M) ≫
        o.theta.inv.app (e.realizeX.derived.obj M)) ≫
      o.opens.jStar'.map B =
      (e.realizeU'.derived.map
          ((Functor.mapDerivedCategorySquareIso
            (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)).hom.app M) ≫
        e.openPull'.hom.app ((finitePull A g).obj M) ≫
        o.opens.jStar'.map (e.pull.hom.app M)) ≫
      o.opens.jStar'.map B := by sorry

end SheafOfModules.OpenTensorNormalization
