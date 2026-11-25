/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowFactors
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryClopenEvaluation
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-!
# Coefficient realization of cartesian open base change

Source: the clopen construction in Stacks 0F7B and Zheng, Construction 4.1.
The comparison concerns only the cartesian lift map, before inserting any clopen projector.
(blueprint: lem-sp-varying-ring-open-base-change-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
private theorem mate_whisker
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : G ⋙ L₂ ⟶ L₁ ⋙ H) (t : G' ⟶ G) (b : H ⟶ H') :
    mateEquiv adj₁ adj₂
        (Functor.whiskerRight t L₂ ≫ a ≫ Functor.whiskerLeft L₁ b) =
      Functor.whiskerLeft R₁ t ≫ mateEquiv adj₁ adj₂ a ≫
        Functor.whiskerRight b R₂ := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  dsimp [mateEquiv]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have ht := adj₂.unit.naturality (t.app (R₁.obj X))
  dsimp at ht
  rw [← reassoc_of% ht]
  slice_lhs 4 5 => rw [← R₂.map_comp, ← b.naturality, R₂.map_comp]

private theorem unmate_paste
    {A B C D a b c d : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category a] [Category b] [Category c] [Category d]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {l₁ : a ⥤ b} {r₁ : b ⥤ a} {l₂ : c ⥤ d} {r₂ : d ⥤ c}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (lev₁ : l₁ ⊣ r₁) (lev₂ : l₂ ⊣ r₂)
    {G : A ⥤ C} {H : B ⥤ D} {g : a ⥤ c} {h : b ⥤ d}
    {E : A ⥤ a} {F : B ⥤ b} {E' : C ⥤ c} {F' : D ⥤ d}
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare g l₁ l₂ h)
    (ξ : TwoSquare E L₁ l₁ F) (ζ : TwoSquare E' L₂ l₂ F')
    (u : G ⋙ E' ⟶ E ⋙ g) (v : H ⋙ F' ⟶ F ⋙ h)
    (hc : ((mateEquiv adj₁ adj₂ α).vComp (mateEquiv adj₂ lev₂ ζ)).whiskerLeft v =
      ((mateEquiv adj₁ lev₁ ξ).vComp (mateEquiv lev₁ lev₂ β)).whiskerRight u) :
    (α.hComp ζ).whiskerBottom v = (ξ.hComp β).whiskerTop u := by
  apply (mateEquiv adj₁ lev₂).injective
  have h₁ := mate_whisker adj₁ lev₂ (α.hComp ζ) (𝟙 _) v
  have h₂ := mate_whisker adj₁ lev₂ (ξ.hComp β) u (𝟙 _)
  have e₁ : mateEquiv adj₁ lev₂ ((α.hComp ζ).whiskerBottom v) =
      (mateEquiv adj₁ lev₂ (α.hComp ζ)).whiskerLeft v := by
    simpa only [Functor.whiskerRight_id', Functor.whiskerLeft_id',
      Category.id_comp, Category.comp_id, TwoSquare.whiskerBottom,
      TwoSquare.whiskerLeft, TwoSquare.mk] using h₁
  have e₂ : mateEquiv adj₁ lev₂ ((ξ.hComp β).whiskerTop u) =
      (mateEquiv adj₁ lev₂ (ξ.hComp β)).whiskerRight u := by
    simpa only [Functor.whiskerRight_id', Functor.whiskerLeft_id',
      Category.id_comp, Category.comp_id, TwoSquare.whiskerTop,
      TwoSquare.whiskerRight, TwoSquare.mk] using h₂
  rw [e₁, e₂, mateEquiv_vcomp, mateEquiv_vcomp]
  exact hc

private theorem openBeta_unit {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) (N : Derived R φ U) :
    (jAdj R φ j').unit.app ((G R φ a).obj N) ≫
        (G R φ j').map
          ((Functor.mapDerivedCategorySquareIso
            (moduleBeta R φ a j' j g h hsq).symm).hom.app N) =
      (G R φ a).map ((jAdj R φ j).unit.app N) ≫
        (Functor.mapDerivedCategorySquareIso
          (moduleSquareG R φ a j' j g h).symm).hom.app ((J R φ j).obj N) := by
  have h₁ := StrictTower.exactAdj_unit (moduleJAdj R φ j)
  have h₂ := StrictTower.exactAdj_unit (moduleJAdj R φ j')
  unfold StrictTower.exactAdj at h₁ h₂
  apply StrictTower.exact_mate (moduleJAdj R φ j) (moduleJAdj R φ j')
    (moduleSquareG R φ a j' j g h).symm (moduleBeta R φ a j' j g h hsq).symm
    (jAdj R φ j) (jAdj R φ j') h₁ h₂
  intro K
  have hk := ((moduleJAdj R φ j').homEquiv _ _).apply_symm_apply
    ((pull R φ a).map ((moduleJAdj R φ j).unit.app K) ≫
      (moduleSquareG R φ a j' j g h).inv.app ((extension R φ j).obj K))
  simpa only [Adjunction.homEquiv_unit, moduleBeta, Iso.symm_hom,
    Iso.symm_inv, asIso_hom, moduleBetaInv, moduleBetaInvApp,
    Functor.id_obj, Functor.comp_obj] using hk

private def coefficientComp (n : ℕ) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Functor.mapDerivedCategoryNatIso (StrictTower.moduleGComp (R n) f g) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

private def composedEvalG (n : ℕ) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (G R φ g ⋙ G R φ f) ⋙ ev R φ X n ≅
      ev R φ Z n ⋙ ((StrictTower.modulePullback (R n) g).mapDerivedCategory ⋙
        (StrictTower.modulePullback (R n) f).mapDerivedCategory) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (G R φ g) (evalG R φ f n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (evalG R φ g n) _ ≪≫ Functor.associator _ _ _

private theorem evalG_comp_iso (n : ℕ) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (gComp R φ f g) (ev R φ X n) ≪≫
        composedEvalG R φ n f g =
      evalG R φ (f ≫ g) n ≪≫
        Functor.isoWhiskerLeft (ev R φ Z n) (coefficientComp R n f g) := by
  exact Functor.mapDerivedCategorySquareIso_comp
    (pull R φ g) (pull R φ f) (pull R φ (f ≫ g))
    (StrictTower.modulePullback (R n) g) (StrictTower.modulePullback (R n) f)
    (StrictTower.modulePullback (R n) (f ≫ g))
    (eval R φ Z n) (eval R φ Y n) (eval R φ X n)
    (moduleEvalG R φ g n) (moduleEvalG R φ f n) (moduleEvalG R φ (f ≫ g) n)
    (moduleGComp R φ f g) (StrictTower.moduleGComp (R n) f g)
    (ordinaryModuleEvalG_comp R φ n f g)

private theorem evalG_eq_iso (n : ℕ) {X Y : Scheme.{u}} (f g : X ⟶ Y) (h : f = g) :
    Functor.isoWhiskerRight (eqToIso (congrArg (G R φ) h)) (ev R φ X n) ≪≫
        evalG R φ g n =
      evalG R φ f n ≪≫ Functor.isoWhiskerLeft (ev R φ Y n)
        (eqToIso (congrArg
          (fun z ↦ (StrictTower.modulePullback (R n) z).mapDerivedCategory) h)) := by
  subst g
  simp

private theorem iso_compositor_cube {C : Type*} [Category C]
    {A B D E X Y Z W : C} (c₁ : A ≅ B) (c₂ : D ≅ E) (s : D ≅ A)
    (d₁ : Z ≅ X) (d₂ : W ≅ Y) (q : W ≅ Z)
    (t₁ : B ≅ X) (t₂ : E ≅ Y) (e₁ : A ≅ Z) (e₂ : D ≅ W)
    (h₁ : c₁ ≪≫ t₁ = e₁ ≪≫ d₁) (h₂ : c₂ ≪≫ t₂ = e₂ ≪≫ d₂)
    (hs : s ≪≫ e₁ = e₂ ≪≫ q) :
    (c₂.symm ≪≫ s ≪≫ c₁) ≪≫ t₁ = t₂ ≪≫ (d₂.symm ≪≫ q ≪≫ d₁) := by
  simp only [Iso.trans_assoc]
  rw [h₁, ← Iso.trans_assoc s, hs]
  have hh := congrArg (fun t ↦ c₂.symm ≪≫ t ≪≫ d₂.symm) h₂
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
    Iso.trans_refl] at hh
  simpa only [Iso.trans_assoc] using congrArg (fun t ↦ t ≪≫ q ≪≫ d₁) hh.symm

private theorem comparison_square
    {C c D : Type*} [Category C] [Category c] [Category D]
    (E : C ⥤ D) (F : c ⥤ D)
    {A B A' B' : C} {a b a' b' : c}
    (c₁ : A ≅ B) (c₂ : A' ≅ B') (s : A' ≅ A)
    (d₁ : a ≅ b) (d₂ : a' ≅ b') (q : a' ≅ a)
    (x : B' ≅ B) (y : b' ≅ b)
    (hx : x = c₂.symm ≪≫ s ≪≫ c₁) (hy : y = d₂.symm ≪≫ q ≪≫ d₁)
    (t₁ : E.obj B ≅ F.obj b) (t₂ : E.obj B' ≅ F.obj b')
    (e₁ : E.obj A ≅ F.obj a) (e₂ : E.obj A' ≅ F.obj a')
    (h₁ : E.mapIso c₁ ≪≫ t₁ = e₁ ≪≫ F.mapIso d₁)
    (h₂ : E.mapIso c₂ ≪≫ t₂ = e₂ ≪≫ F.mapIso d₂)
    (hs : E.mapIso s ≪≫ e₁ = e₂ ≪≫ F.mapIso q) :
    E.mapIso x ≪≫ t₁ = t₂ ≪≫ F.mapIso y := by
  rw [hx, hy]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm]
  exact iso_compositor_cube (E.mapIso c₁) (E.mapIso c₂) (E.mapIso s)
    (F.mapIso d₁) (F.mapIso d₂) (F.mapIso q) t₁ t₂ e₁ e₂ h₁ h₂ hs

private theorem evalG_square_iso (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    (h : a ≫ i = b ≫ p) :
    Functor.isoWhiskerRight
        (Functor.mapDerivedCategorySquareIso (moduleSquareG R φ a b i p h))
        (ev R φ V n) ≪≫ composedEvalG R φ n a i =
      composedEvalG R φ n b p ≪≫ Functor.isoWhiskerLeft (ev R φ T n)
        (Functor.mapDerivedCategorySquareIso (StrictTower.moduleSquareG (R n) a b i p h)) := by
  have hv := StrictTower.derivedSquare_comp
    (pull R φ p) (pull R φ b) (pull R φ i) (pull R φ a)
    (pull R φ (b ≫ p)) (pull R φ (a ≫ i))
    (moduleGComp R φ b p) (moduleGComp R φ a i)
    (congrArg (pull R φ) h.symm) (congrArg (G R φ) h.symm)
  have hl := StrictTower.derivedSquare_comp
    (StrictTower.modulePullback (R n) p) (StrictTower.modulePullback (R n) b)
    (StrictTower.modulePullback (R n) i) (StrictTower.modulePullback (R n) a)
    (StrictTower.modulePullback (R n) (b ≫ p))
    (StrictTower.modulePullback (R n) (a ≫ i))
    (StrictTower.moduleGComp (R n) b p) (StrictTower.moduleGComp (R n) a i)
    (congrArg (StrictTower.modulePullback (R n)) h.symm)
    (congrArg (fun z ↦ (StrictTower.modulePullback (R n) z).mapDerivedCategory) h.symm)
  have hv' : Functor.mapDerivedCategorySquareIso (moduleSquareG R φ a b i p h) =
      (gComp R φ b p).symm ≪≫ eqToIso (congrArg (G R φ) h.symm) ≪≫
        gComp R φ a i := by
    apply Iso.ext
    rw [moduleSquareG_eq]
    exact hv
  have hl' : Functor.mapDerivedCategorySquareIso (StrictTower.moduleSquareG (R n) a b i p h) =
      (coefficientComp R n b p).symm ≪≫
        eqToIso (congrArg
          (fun z ↦ (StrictTower.modulePullback (R n) z).mapDerivedCategory) h.symm) ≪≫
        coefficientComp R n a i := by
    apply Iso.ext
    rw [StrictTower.moduleSquareG_eq]
    exact hl
  exact comparison_square
    ((Functor.whiskeringRight (Derived R φ T) (Derived R φ V)
      (DerivedCategory (StrictTower.Modules (R n) V))).obj (ev R φ V n))
    ((Functor.whiskeringLeft (Derived R φ T)
      (DerivedCategory (StrictTower.Modules (R n) T))
      (DerivedCategory (StrictTower.Modules (R n) V))).obj (ev R φ T n))
    (gComp R φ a i) (gComp R φ b p) (eqToIso (congrArg (G R φ) h.symm))
    (coefficientComp R n a i) (coefficientComp R n b p)
    (eqToIso (congrArg
      (fun z ↦ (StrictTower.modulePullback (R n) z).mapDerivedCategory) h.symm))
    (Functor.mapDerivedCategorySquareIso (moduleSquareG R φ a b i p h))
    (Functor.mapDerivedCategorySquareIso (StrictTower.moduleSquareG (R n) a b i p h))
    hv' hl'
    (composedEvalG R φ n a i) (composedEvalG R φ n b p)
    (evalG R φ (a ≫ i) n) (evalG R φ (b ≫ p) n)
    (evalG_comp_iso R φ n a i) (evalG_comp_iso R φ n b p)
    (evalG_eq_iso R φ n (b ≫ p) (a ≫ i) h.symm)

private theorem inverse_square {C : Type*} [Category C]
    {A B D E : C} (e : A ≅ B) (f : D ≅ E) (a : B ≅ E) (b : A ≅ D)
    (h : e ≪≫ a = b ≪≫ f) : e.symm ≪≫ b = a ≪≫ f.symm := by
  have hh := congrArg (fun t ↦ e.symm ≪≫ t ≪≫ f.symm) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
    Iso.trans_refl] using hh.symm

private theorem evalG_square_inv (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    (h : a ≫ i = b ≫ p) (N : Derived R φ T) :
    (ev R φ V n).map
        ((Functor.mapDerivedCategorySquareIso
          (moduleSquareG R φ a b i p h)).inv.app N) ≫
        (evalG R φ b n).hom.app ((G R φ p).obj N) ≫
        (StrictTower.modulePullback (R n) b).mapDerivedCategory.map
          ((evalG R φ p n).hom.app N) =
      (evalG R φ a n).hom.app ((G R φ i).obj N) ≫
        (StrictTower.modulePullback (R n) a).mapDerivedCategory.map
          ((evalG R φ i n).hom.app N) ≫
        (Functor.mapDerivedCategorySquareIso
          (StrictTower.moduleSquareG (R n) a b i p h)).inv.app
          ((ev R φ T n).obj N) := by
  have hh := inverse_square _ _ _ _ (evalG_square_iso R φ n a b i p h)
  have hc := congrArg (fun e ↦ e.hom.app N) hh
  simpa only [composedEvalG, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hc

private def levelBetaInv (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p) :
    (StrictTower.modulePullback (R n) a).mapDerivedCategory ⋙
        (StrictTower.moduleJ (R n) b).mapDerivedCategory ⟶
      (StrictTower.moduleJ (R n) i).mapDerivedCategory ⋙
        (StrictTower.modulePullback (R n) p).mapDerivedCategory :=
  ((mateEquiv (levelJAdj R i n) (levelJAdj R b n)).symm
    (Functor.mapDerivedCategorySquareIso
      (StrictTower.moduleSquareG (R n) a b i p h)).inv)

private theorem betaInv_mate {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p)
    (hsq : IsPullback a b i p) :
    mateEquiv (jAdj R φ i) (jAdj R φ b)
      (Functor.mapDerivedCategorySquareIso (moduleBeta R φ a b i p h hsq)).inv =
      (Functor.mapDerivedCategorySquareIso (moduleSquareG R φ a b i p h)).inv := by
  apply mateEquiv_eq_of_unit
  intro N
  have hh := openBeta_unit R φ a b i p h hsq N
  rw [Functor.square_symm_hom, Functor.square_symm_hom] at hh
  exact hh.symm

private theorem evalBetaInv (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p)
    (hsq : IsPullback a b i p) (N : Derived R φ S) :
    (StrictTower.moduleJ (R n) b).mapDerivedCategory.map
        ((evalG R φ a n).hom.app N) ≫
        (levelBetaInv R n a b i p h).app ((ev R φ S n).obj N) ≫
        (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
          ((evalJInv R φ i n).app N) =
      (evalJInv R φ b n).app ((G R φ a).obj N) ≫
        (ev R φ W n).map
          ((Functor.mapDerivedCategorySquareIso (moduleBeta R φ a b i p h hsq)).inv.app N) ≫
        (evalG R φ p n).hom.app ((J R φ i).obj N) := by
  have hc := unmate_paste (jAdj R φ i) (jAdj R φ b)
    (levelJAdj R i n) (levelJAdj R b n)
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (moduleBeta R φ a b i p h hsq)).inv)
    (TwoSquare.mk _ _ _ _ (levelBetaInv R n a b i p h))
    (TwoSquare.mk _ _ _ _ (evalJInv R φ i n))
    (TwoSquare.mk _ _ _ _ (evalJInv R φ b n))
    (evalG R φ a n).hom (evalG R φ p n).hom
    (by
      rw [betaInv_mate]
      simp only [levelBetaInv, evalJInv, Equiv.apply_symm_apply]
      refine NatTrans.ext (funext fun M ↦ ?_)
      simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
        TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id,
        Category.assoc] using evalG_square_inv R φ n a b i p h M)
  have he := congrArg (fun w ↦ w.app N) hc
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using he.symm

private theorem exactEvaluation_mate
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
    {L : C ⥤ D} {P : D ⥤ C}
    [L.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (adj : L ⊣ P) :
    mateEquiv (StrictTower.exactAdj (adj.whiskerRight ℕᵒᵖ)) (StrictTower.exactAdj adj)
      (StrictTower.evalD L 0).inv = (StrictTower.evalD P 0).hom := by
  apply mateEquiv_eq_of_unit
  intro N
  have hh := StrictTower.exact_mate (adj.whiskerRight ℕᵒᵖ) adj
    (u := StrictTower.E C 0) (v := StrictTower.E D 0)
    (Iso.refl _) (Iso.refl _)
    (StrictTower.exactAdj (adj.whiskerRight ℕᵒᵖ)) (StrictTower.exactAdj adj)
    (StrictTower.exactAdj_unit _) (StrictTower.exactAdj_unit _)
    (by
      intro K
      simp [StrictTower.E, Adjunction.whiskerRight]) N
  simpa only [StrictTower.evalD, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_refl, Iso.trans_refl, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id] using hh.symm

private theorem strictOpen_mate (n : ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    mateEquiv (StrictTower.jAdj (R n) j) (levelJAdj R j n)
      (StrictTower.evalJ (R n) j 0).inv = (StrictTower.evalG (R n) j 0).hom := by
  have hh := exactEvaluation_mate (StrictTower.moduleJAdj (R n) j)
  rw [StrictTower.exactAdj_jAdj] at hh
  rw [StrictTower.evalG_eq, StrictTower.evalJ_eq]
  unfold StrictTower.exactAdj at hh
  exact hh

private theorem strictSquareInv_eval (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    (h : a ≫ i = b ≫ p) (N : StrictTower.Derived (R n) T) :
    (StrictTower.ev (R n) V 0).map ((StrictTower.squareG (R n) a b i p h).inv.app N) ≫
        (StrictTower.evalG (R n) b 0).hom.app ((StrictTower.G (R n) p).obj N) ≫
        (StrictTower.modulePullback (R n) b).mapDerivedCategory.map
          ((StrictTower.evalG (R n) p 0).hom.app N) =
      (StrictTower.evalG (R n) a 0).hom.app ((StrictTower.G (R n) i).obj N) ≫
        (StrictTower.modulePullback (R n) a).mapDerivedCategory.map
          ((StrictTower.evalG (R n) i 0).hom.app N) ≫
        (Functor.mapDerivedCategorySquareIso
          (StrictTower.moduleSquareG (R n) a b i p h)).inv.app
          ((StrictTower.ev (R n) T 0).obj N) := by
  have he := StrictTower.evalD_square (StrictTower.modulePullback (R n) i)
    (StrictTower.modulePullback (R n) a) (StrictTower.modulePullback (R n) p)
    (StrictTower.modulePullback (R n) b)
    (StrictTower.moduleSquareG (R n) a b i p h).symm N 0
  rw [StrictTower.towerSquare_symm, Functor.square_symm_hom,
    Functor.square_symm_hom] at he
  have hs : Functor.mapDerivedCategorySquareIso
      (StrictTower.towerSquare (StrictTower.modulePullback (R n) p)
        (StrictTower.modulePullback (R n) b) (StrictTower.modulePullback (R n) i)
        (StrictTower.modulePullback (R n) a)
        (StrictTower.moduleSquareG (R n) a b i p h)) =
      StrictTower.squareG (R n) a b i p h :=
    (Iso.ext (StrictTower.squareG_lift (R n) a b i p h)).symm
  rw [hs] at he
  rw [← StrictTower.evalG_eq, ← StrictTower.evalG_eq,
    ← StrictTower.evalG_eq, ← StrictTower.evalG_eq] at he
  exact he

private theorem strictBetaInv_mate {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p) (n : ℕ) :
    mateEquiv (StrictTower.jAdj (R n) i) (StrictTower.jAdj (R n) b)
      (StrictTower.betaInv (R n) a b i p h) =
      (StrictTower.squareG (R n) a b i p h).inv := by
  apply mateEquiv_eq_of_unit
  intro N
  symm
  change (StrictTower.jAdj (R n) b).homEquiv _ _
    (StrictTower.betaInvApp (R n) a b i p h N) = _
  exact ((StrictTower.jAdj (R n) b).homEquiv _ _).apply_symm_apply _

private theorem strictEvalBetaInv (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p)
    (N : StrictTower.Derived (R n) S) :
    (StrictTower.moduleJ (R n) b).mapDerivedCategory.map
        ((StrictTower.evalG (R n) a 0).hom.app N) ≫
        (levelBetaInv R n a b i p h).app ((StrictTower.ev (R n) S 0).obj N) ≫
        (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
          ((StrictTower.evalJ (R n) i 0).inv.app N) =
      (StrictTower.evalJ (R n) b 0).inv.app ((StrictTower.G (R n) a).obj N) ≫
        (StrictTower.ev (R n) W 0).map ((StrictTower.betaInv (R n) a b i p h).app N) ≫
        (StrictTower.evalG (R n) p 0).hom.app ((StrictTower.J (R n) i).obj N) := by
  have hc := unmate_paste (StrictTower.jAdj (R n) i) (StrictTower.jAdj (R n) b)
    (levelJAdj R i n) (levelJAdj R b n)
    (TwoSquare.mk _ _ _ _ (StrictTower.betaInv (R n) a b i p h))
    (TwoSquare.mk _ _ _ _ (levelBetaInv R n a b i p h))
    (TwoSquare.mk _ _ _ _ (StrictTower.evalJ (R n) i 0).inv)
    (TwoSquare.mk _ _ _ _ (StrictTower.evalJ (R n) b 0).inv)
    (StrictTower.evalG (R n) a 0).hom (StrictTower.evalG (R n) p 0).hom
    (by
      rw [strictBetaInv_mate, strictOpen_mate, strictOpen_mate]
      simp only [levelBetaInv, Equiv.apply_symm_apply]
      refine NatTrans.ext (funext fun M ↦ ?_)
      simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
        TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id,
        Category.assoc] using strictSquareInv_eval R n a b i p h M)
  have he := congrArg (fun w ↦ w.app N) hc
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using he.symm

private theorem isIso_app_of_objIso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (η : F ⟶ G) {X Y : C} (e : X ≅ Y) [IsIso (η.app X)] : IsIso (η.app Y) := by
  have hh : IsIso (F.map e.hom ≫ η.app Y) := by
    rw [η.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map e.hom) _

private theorem levelBetaInv_isIso (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p)
    (hsq : IsPullback a b i p) : IsIso (levelBetaInv R n a b i p h) := by
  have hi (N : StrictTower.Derived (R n) S) :
      IsIso ((levelBetaInv R n a b i p h).app ((StrictTower.ev (R n) S 0).obj N)) := by
    have := StrictTower.betaInv_isIso (R n) a b i p h hsq
    have he := strictEvalBetaInv R n a b i p h N
    have hh : IsIso
        ((StrictTower.moduleJ (R n) b).mapDerivedCategory.map
          ((StrictTower.evalG (R n) a 0).hom.app N) ≫
          (levelBetaInv R n a b i p h).app ((StrictTower.ev (R n) S 0).obj N) ≫
          (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
            ((StrictTower.evalJ (R n) i 0).inv.app N)) := by
      rw [he]
      infer_instance
    have : IsIso
        ((levelBetaInv R n a b i p h).app ((StrictTower.ev (R n) S 0).obj N) ≫
          (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
            ((StrictTower.evalJ (R n) i 0).inv.app N)) :=
      IsIso.of_isIso_comp_left
        ((StrictTower.moduleJ (R n) b).mapDerivedCategory.map
          ((StrictTower.evalG (R n) a 0).hom.app N)) _
    exact IsIso.of_isIso_comp_right _
      ((StrictTower.modulePullback (R n) p).mapDerivedCategory.map
        ((StrictTower.evalJ (R n) i 0).inv.app N))
  have hall (M : DerivedCategory (StrictTower.Modules (R n) S)) :
      IsIso ((levelBetaInv R n a b i p h).app M) := by
    let N := (constantDerived (R n) S).obj M
    let e := (constantEval (R n) S).app M
    have : IsIso ((levelBetaInv R n a b i p h).app
        ((constantDerived (R n) S ⋙ StrictTower.ev (R n) S 0).obj M)) := by
      change IsIso ((levelBetaInv R n a b i p h).app ((StrictTower.ev (R n) S 0).obj N))
      exact hi N
    exact isIso_app_of_objIso (levelBetaInv R n a b i p h) e
  exact NatIso.isIso_of_isIso_app _

private theorem inverse_beta_square {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ Y₁ Y₂ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₀ ≅ Y₁) (e : Y₁ ≅ Y₂) (f : Y₂ ≅ X₃)
    (h : c.hom ≫ f.inv ≫ e.inv = b.inv ≫ a.inv ≫ d.hom) :
    a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom := by
  have hh := congrArg (fun t ↦ a.hom ≫ b.hom ≫ t ≫ e.hom ≫ f.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using hh

private theorem varyingBetaForward (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p)
    (hsq : IsPullback a b i p) [IsIso (levelBetaInv R n a b i p h)]
    (N : Derived R φ S) :
    (ev R φ W n).map
        ((Functor.mapDerivedCategorySquareIso (moduleBeta R φ a b i p h hsq)).hom.app N) ≫
        (evalJ R φ b n).hom.app ((G R φ a).obj N) ≫
        (StrictTower.moduleJ (R n) b).mapDerivedCategory.map
          ((evalG R φ a n).hom.app N) =
      (evalG R φ p n).hom.app ((J R φ i).obj N) ≫
        (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
          ((evalJ R φ i n).hom.app N) ≫
        (asIso (levelBetaInv R n a b i p h)).inv.app ((ev R φ S n).obj N) := by
  have he := inverse_beta_square
    ((ev R φ W n).mapIso
      ((Functor.mapDerivedCategorySquareIso (moduleBeta R φ a b i p h hsq)).app N))
    ((evalJ R φ b n).app ((G R φ a).obj N))
    ((StrictTower.moduleJ (R n) b).mapDerivedCategory.mapIso ((evalG R φ a n).app N))
    ((evalG R φ p n).app ((J R φ i).obj N))
    ((StrictTower.modulePullback (R n) p).mapDerivedCategory.mapIso ((evalJ R φ i n).app N))
    ((asIso (levelBetaInv R n a b i p h)).symm.app ((ev R φ S n).obj N))
    (by
      simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
        Iso.symm_inv, asIso_hom, evalJ] using evalBetaInv R φ n a b i p h hsq N)
  simpa only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom] using he

private theorem strictBetaForward (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p)
    (hsq : IsPullback a b i p) [IsIso (levelBetaInv R n a b i p h)]
    (N : StrictTower.Derived (R n) S) :
    (StrictTower.ev (R n) W 0).map ((StrictTower.beta (R n) a b i p h hsq).hom.app N) ≫
        (StrictTower.evalJ (R n) b 0).hom.app ((StrictTower.G (R n) a).obj N) ≫
        (StrictTower.moduleJ (R n) b).mapDerivedCategory.map
          ((StrictTower.evalG (R n) a 0).hom.app N) =
      (StrictTower.evalG (R n) p 0).hom.app ((StrictTower.J (R n) i).obj N) ≫
        (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
          ((StrictTower.evalJ (R n) i 0).hom.app N) ≫
        (asIso (levelBetaInv R n a b i p h)).inv.app ((StrictTower.ev (R n) S 0).obj N) := by
  have he := inverse_beta_square
    ((StrictTower.ev (R n) W 0).mapIso ((StrictTower.beta (R n) a b i p h hsq).app N))
    ((StrictTower.evalJ (R n) b 0).app ((StrictTower.G (R n) a).obj N))
    ((StrictTower.moduleJ (R n) b).mapDerivedCategory.mapIso
      ((StrictTower.evalG (R n) a 0).app N))
    ((StrictTower.evalG (R n) p 0).app ((StrictTower.J (R n) i).obj N))
    ((StrictTower.modulePullback (R n) p).mapDerivedCategory.mapIso
      ((StrictTower.evalJ (R n) i 0).app N))
    ((asIso (levelBetaInv R n a b i p h)).symm.app ((StrictTower.ev (R n) S 0).obj N))
    (by
      simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
        Iso.symm_inv, asIso_hom, StrictTower.beta] using
        strictEvalBetaInv R n a b i p h N)
  simpa only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom] using he

/-- Coefficient evaluation preserves the cartesian open base-change comparison,
using the specified pullback and open-extension comparisons.
Source: Stacks 09AE and 03DI; Zheng, Construction 4.1
(blueprint: lem-sp-varying-ring-open-base-change-evaluation).
Proof: the ordinary unit-normalized pullback comparison preserves composition.
The exact-square composition theorem localizes that natural-isomorphism equation
before taking components. Apply it to the two paths around the square, including
the equality transport; this identifies evaluation of the inverse square map.
The inverse beta is the open-adjunction mate of that square map: exact localization
preserves its defining unit equation. Open evaluation is itself the inverse mate
of pullback evaluation. The mate interchange law therefore gives evaluation of
inverse beta with the single-coefficient open mate of the single-coefficient
square map. For strict towers the pullback-square equation is termwise evaluation,
and its open mate equation follows from exact localization of the ordinary unit.
The same mate interchange gives the identical single-coefficient inverse map.
Cartesianness makes strict inverse beta invertible. Cancel the other invertible
comparison factors to see that the single-coefficient mate is invertible at every
evaluated strict tower. Every single-coefficient derived object is isomorphic to
the evaluation of its constant derived tower. Naturality along constantEval thus
proves invertibility at every object, without asserting faithfulness of evaluation.
Take the inverse of this specified single-coefficient mate. Multiplying the two
inverse comparison equations by the six comparison isomorphisms gives exactly the
two displayed forward equations. No finiteness or properness assumption is used. -/
theorem openBaseChangeEvaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    (h : r ≫ i = k ≫ p) (hsq : IsPullback r k i p) (n : ℕ) :
    ∃ a : (StrictTower.moduleJ (R n) i).mapDerivedCategory ⋙
          (StrictTower.modulePullback (R n) p).mapDerivedCategory ⟶
        (StrictTower.modulePullback (R n) r).mapDerivedCategory ⋙
          (StrictTower.moduleJ (R n) k).mapDerivedCategory,
      (∀ N : Derived R φ S,
        (ev R φ W n).map ((openBaseChange R φ r k i p h hsq).app N) ≫
            (evalJ R φ k n).hom.app ((G R φ r).obj N) ≫
            (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
              ((evalG R φ r n).hom.app N) =
          (evalG R φ p n).hom.app ((J R φ i).obj N) ≫
            (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
              ((evalJ R φ i n).hom.app N) ≫ a.app ((ev R φ S n).obj N)) ∧
      (∀ N : StrictTower.Derived (R n) S,
        (StrictTower.ev (R n) W 0).map ((StrictTower.beta (R n) r k i p h hsq).hom.app N) ≫
            (StrictTower.evalJ (R n) k 0).hom.app ((StrictTower.G (R n) r).obj N) ≫
            (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
              ((StrictTower.evalG (R n) r 0).hom.app N) =
          (StrictTower.evalG (R n) p 0).hom.app ((StrictTower.J (R n) i).obj N) ≫
            (StrictTower.modulePullback (R n) p).mapDerivedCategory.map
              ((StrictTower.evalJ (R n) i 0).hom.app N) ≫
            a.app ((StrictTower.ev (R n) S 0).obj N)) := by
  have := levelBetaInv_isIso R n r k i p h hsq
  refine ⟨(asIso (levelBetaInv R n r k i p h)).inv, ?_, ?_⟩
  · intro N
    change (ev R φ W n).map
        ((Functor.mapDerivedCategorySquareIso (moduleBeta R φ r k i p h hsq)).hom.app N) ≫
        _ = _
    exact varyingBetaForward R φ n r k i p h hsq N
  · intro N
    exact strictBetaForward R n r k i p h hsq N

end AlgebraicGeometry.ProEtale.VaryingRing
