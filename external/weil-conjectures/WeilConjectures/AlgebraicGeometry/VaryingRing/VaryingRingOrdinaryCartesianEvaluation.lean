/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryEvaluationComparisons
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryComparisonNormalization
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryOpenUnit
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Ordinary realization of cartesian open base change

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DI and 09AE.
(blueprint: lem-sp-varying-ring-ordinary-cartesian-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] ordinaryRealization ordinaryPullComparison ordinaryOpenComparison
  moduleGComp Functor.mapDerivedCategory StrictTower.G StrictTower.J StrictTower.gComp
  Functor.leftAdjoint StrictTower.towers_hasDerivedCategory
  Scheme.proEtaleRingModules_hasDerivedCategory

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
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk, Category.assoc] using
    mateEquiv_whiskerTop_whiskerBottom adj₁ adj₂ (TwoSquare.mk _ _ _ _ a) t b

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

private theorem morphism_compositor_cube {C : Type*} [Category C]
    {A B D E X Y Z W : C}
    (c₁ : A ⟶ B) (c₂ : D ⟶ E) (c₂i : E ⟶ D) (s : D ⟶ A)
    (d₁ : Z ⟶ X) (d₂ : W ⟶ Y) (d₂i : Y ⟶ W) (q : W ⟶ Z)
    (t₁ : B ⟶ X) (t₂ : E ⟶ Y) (e₁ : A ⟶ Z) (e₂ : D ⟶ W)
    (hc₂ : c₂i ≫ c₂ = 𝟙 E) (hd₂ : d₂ ≫ d₂i = 𝟙 W)
    (h₁ : c₁ ≫ t₁ = e₁ ≫ d₁) (h₂ : c₂ ≫ t₂ = e₂ ≫ d₂)
    (hs : s ≫ e₁ = e₂ ≫ q) :
    c₂i ≫ s ≫ c₁ ≫ t₁ = t₂ ≫ d₂i ≫ q ≫ d₁ := by
  rw [h₁, ← Category.assoc s, hs]
  have hh := congrArg (fun t ↦ c₂i ≫ t ≫ d₂i) h₂
  simp only [Category.assoc] at hh
  rw [← Category.assoc c₂i c₂, hc₂, Category.id_comp, hd₂, Category.comp_id] at hh
  simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ q ≫ d₁) hh.symm

private theorem comparison_square_hom
    {C D : Type*} [Category C] [Category D] (E : C ⥤ D)
    {A B A' B' : C} {a b a' b' : D}
    (c₁ : A ⟶ B) (c₂ : A' ⟶ B') (c₂i : B' ⟶ A') (s : A' ⟶ A)
    (d₁ : a ⟶ b) (d₂ : a' ⟶ b') (d₂i : b' ⟶ a') (q : a' ⟶ a)
    (x : B' ⟶ B) (y : b' ⟶ b)
    (hx : x = c₂i ≫ s ≫ c₁) (hy : y = d₂i ≫ q ≫ d₁)
    (t₁ : E.obj B ⟶ b) (t₂ : E.obj B' ⟶ b')
    (e₁ : E.obj A ⟶ a) (e₂ : E.obj A' ⟶ a')
    (hc₂ : c₂i ≫ c₂ = 𝟙 B') (hd₂ : d₂ ≫ d₂i = 𝟙 a')
    (h₁ : E.map c₁ ≫ t₁ = e₁ ≫ d₁)
    (h₂ : E.map c₂ ≫ t₂ = e₂ ≫ d₂)
    (hs : E.map s ≫ e₁ = e₂ ≫ q) :
    E.map x ≫ t₁ = t₂ ≫ y := by
  have hh := morphism_compositor_cube (E.map c₁) (E.map c₂) (E.map c₂i) (E.map s)
    d₁ d₂ d₂i q t₁ t₂ e₁ e₂
    (by rw [← E.map_comp, hc₂, E.map_id]) hd₂ h₁ h₂ hs
  rw [hx, hy]
  simpa only [Functor.map_comp, Category.assoc] using hh

private theorem square_hom_formula
    {C D : Type*} [Category C] [Category D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    (c₁ : F₁ ≅ F₂) (c₂ : F₃ ≅ F₄) (s : F₃ ≅ F₁) (x : F₄ ≅ F₂)
    (hx : x = c₂.symm ≪≫ s ≪≫ c₁) (N : C) :
    x.hom.app N = c₂.inv.app N ≫ s.hom.app N ≫ c₁.hom.app N := by
  rw [hx]
  rfl

private theorem inverse_square_hom {C : Type*} [Category C]
    {A B D E : C} (e : A ⟶ B) (ei : B ⟶ A) (f : D ⟶ E) (fi : E ⟶ D)
    (a : B ⟶ E) (b : A ⟶ D)
    (he : ei ≫ e = 𝟙 B) (hf : f ≫ fi = 𝟙 D)
    (h : e ≫ a = b ≫ f) : ei ≫ b = a ≫ fi := by
  have hh := congrArg (fun t ↦ ei ≫ t ≫ fi) h
  simp only [Category.assoc] at hh
  rw [← Category.assoc ei e, he, Category.id_comp, hf, Category.comp_id] at hh
  exact hh.symm

private theorem inverse_beta_square {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ Y₁ Y₂ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₀ ≅ Y₁) (e : Y₁ ≅ Y₂) (f : Y₂ ≅ X₃)
    (h : c.hom ≫ f.inv ≫ e.inv = b.inv ≫ a.inv ≫ d.hom) :
    a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom := by
  have hh := congrArg (fun t ↦ a.hom ≫ b.hom ≫ t ≫ e.hom ≫ f.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using hh

private theorem comparison_of_inverse
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    {R₀ : C ⥤ A} {P₀ : D ⥤ B} {K : A ⥤ B} {I : C ⥤ D}
    {r : C' ⥤ A'} {p : D' ⥤ B'} {k : A' ⥤ B'} {i : C' ⥤ D'}
    (eR : R₀ ⋙ EA ≅ EC ⋙ r) (eP : P₀ ⋙ EB ≅ ED ⋙ p)
    (eK : K ⋙ EB ≅ EA ⋙ k) (eI : I ⋙ ED ≅ EC ⋙ i)
    (a : I ⋙ P₀ ≅ R₀ ⋙ K) (a' : i ⋙ p ≅ r ⋙ k)
    (h : ∀ N : C,
      k.map (eR.hom.app N) ≫ a'.inv.app (EC.obj N) ≫ p.map (eI.inv.app N) =
        eK.inv.app (R₀.obj N) ≫ EB.map (a.inv.app N) ≫ eP.hom.app (I.obj N)) :
    OrdinarySquareComparison eR eP eK eI a.hom a'.hom := by
  constructor
  intro N
  exact inverse_beta_square (EB.mapIso (a.app N)) (eK.app (R₀.obj N))
    (k.mapIso (eR.app N)) (eP.app (I.obj N)) (p.mapIso (eI.app N))
    (a'.app (EC.obj N)) (h N)

private theorem ordinaryPull_eq_component (n : ℕ)
    (gIso : OrdinaryPullComparison R φ n) {X Y : Scheme.{u}}
    (f g : X ⟶ Y) (h : f = g) (N : Modules R φ Y) :
    (ordinaryRealization R φ n X).map
        ((eqToIso (congrArg (pull R φ) h)).hom.app N) ≫
        (gIso X Y g).hom.app N =
      (gIso X Y f).hom.app N ≫
        (eqToIso (congrArg (StrictTower.G (R n)) h)).hom.app
          ((ordinaryRealization R φ n Y).obj N) := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  rw [(ordinaryRealization R φ n X).map_id, Category.id_comp]
  exact (Category.comp_id ((gIso X Y f).hom.app N)).symm

private theorem ordinaryPull_square_hom (n : ℕ)
    (gIso : OrdinaryPullComparison R φ n) (hc : OrdinaryPullComposition R φ n gIso)
    {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    (h : a ≫ i = b ≫ p) (N : Modules R φ T) :
    (ordinaryRealization R φ n V).map ((moduleSquareG R φ a b i p h).hom.app N) ≫
        (gIso V S a).hom.app ((pull R φ i).obj N) ≫
        (StrictTower.G (R n) a).map ((gIso S T i).hom.app N) =
      ((gIso V W b).hom.app ((pull R φ p).obj N) ≫
        (StrictTower.G (R n) b).map ((gIso W T p).hom.app N)) ≫
        (StrictTower.squareG (R n) a b i p h).hom.app
          ((ordinaryRealization R φ n T).obj N) := by
  convert comparison_square_hom (ordinaryRealization R φ n V)
    ((moduleGComp R φ a i).hom.app N) ((moduleGComp R φ b p).hom.app N)
    ((moduleGComp R φ b p).inv.app N)
    ((eqToIso (congrArg (pull R φ) h.symm)).hom.app N)
    ((StrictTower.gComp (R n) a i).hom.app ((ordinaryRealization R φ n T).obj N))
    ((StrictTower.gComp (R n) b p).hom.app ((ordinaryRealization R φ n T).obj N))
    ((StrictTower.gComp (R n) b p).inv.app ((ordinaryRealization R φ n T).obj N))
    ((eqToIso (congrArg (StrictTower.G (R n)) h.symm)).hom.app
      ((ordinaryRealization R φ n T).obj N))
    ((moduleSquareG R φ a b i p h).hom.app N)
    ((StrictTower.squareG (R n) a b i p h).hom.app ((ordinaryRealization R φ n T).obj N))
    (square_hom_formula (moduleGComp R φ a i) (moduleGComp R φ b p)
      (eqToIso (congrArg (pull R φ) h.symm)) (moduleSquareG R φ a b i p h)
      (moduleSquareG_eq R φ a b i p h) N)
    (square_hom_formula (StrictTower.gComp (R n) a i) (StrictTower.gComp (R n) b p)
      (eqToIso (congrArg (StrictTower.G (R n)) h.symm))
      (StrictTower.squareG (R n) a b i p h) rfl ((ordinaryRealization R φ n T).obj N))
    ((gIso V S a).hom.app ((pull R φ i).obj N) ≫
      (StrictTower.G (R n) a).map ((gIso S T i).hom.app N))
    ((gIso V W b).hom.app ((pull R φ p).obj N) ≫
      (StrictTower.G (R n) b).map ((gIso W T p).hom.app N))
    ((gIso V T (a ≫ i)).hom.app N) ((gIso V T (b ≫ p)).hom.app N)
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) (hc a i N) (hc b p N)
    (ordinaryPull_eq_component R φ n gIso (b ≫ p) (a ≫ i) h.symm N) using 1

private theorem ordinaryPull_square_inv (n : ℕ)
    (gIso : OrdinaryPullComparison R φ n) (hc : OrdinaryPullComposition R φ n gIso)
    {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    (h : a ≫ i = b ≫ p) (N : Modules R φ T) :
    (ordinaryRealization R φ n V).map ((moduleSquareG R φ a b i p h).inv.app N) ≫
        (gIso V W b).hom.app ((pull R φ p).obj N) ≫
        (StrictTower.G (R n) b).map ((gIso W T p).hom.app N) =
      (gIso V S a).hom.app ((pull R φ i).obj N) ≫
        (StrictTower.G (R n) a).map ((gIso S T i).hom.app N) ≫
        (StrictTower.squareG (R n) a b i p h).inv.app
          ((ordinaryRealization R φ n T).obj N) := by
  have hh := inverse_square_hom
    ((ordinaryRealization R φ n V).map ((moduleSquareG R φ a b i p h).hom.app N))
    ((ordinaryRealization R φ n V).map ((moduleSquareG R φ a b i p h).inv.app N))
    ((StrictTower.squareG (R n) a b i p h).hom.app ((ordinaryRealization R φ n T).obj N))
    ((StrictTower.squareG (R n) a b i p h).inv.app ((ordinaryRealization R φ n T).obj N)) _ _
    (by rw [← (ordinaryRealization R φ n V).map_comp, Iso.inv_hom_id_app,
      (ordinaryRealization R φ n V).map_id])
    (Iso.hom_inv_id_app _ _) (ordinaryPull_square_hom R φ n gIso hc a b i p h N)
  simpa only [Category.assoc] using hh

private theorem ordinaryBetaInv_mate {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p) :
    mateEquiv (moduleJAdj R φ i) (moduleJAdj R φ b)
      (moduleBetaInv R φ a b i p h) = (moduleSquareG R φ a b i p h).inv := by
  apply mateEquiv_eq_of_unit
  intro N
  symm
  change (moduleJAdj R φ b).homEquiv _ _ (moduleBetaInvApp R φ a b i p h N) = _
  exact ((moduleJAdj R φ b).homEquiv _ _).apply_symm_apply _

private theorem strictBetaInv_mate (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p) :
    mateEquiv (StrictTower.jAdj (R n) i) (StrictTower.jAdj (R n) b)
      (StrictTower.betaInv (R n) a b i p h) =
      (StrictTower.squareG (R n) a b i p h).inv := by
  apply mateEquiv_eq_of_unit
  intro N
  symm
  change (StrictTower.jAdj (R n) b).homEquiv _ _
    (StrictTower.betaInvApp (R n) a b i p h N) = _
  exact ((StrictTower.jAdj (R n) b).homEquiv _ _).apply_symm_apply _

private theorem ordinaryBeta_inv (n : ℕ)
    (gIso : OrdinaryPullComparison R φ n) (jIso : OrdinaryOpenComparison R φ n)
    (hc : OrdinaryPullComposition R φ n gIso)
    (hm : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
      mateEquiv (moduleJAdj R φ j) (StrictTower.jAdj (R n) j) (jIso U X j).inv =
        (gIso U X j).hom)
    {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i] (h : a ≫ i = b ≫ p)
    (N : Modules R φ S) :
    (StrictTower.J (R n) b).map ((gIso V S a).hom.app N) ≫
        (StrictTower.betaInv (R n) a b i p h).app ((ordinaryRealization R φ n S).obj N) ≫
        (StrictTower.G (R n) p).map ((jIso S T i).inv.app N) =
      (jIso V W b).inv.app ((pull R φ a).obj N) ≫
        (ordinaryRealization R φ n W).map ((moduleBetaInv R φ a b i p h).app N) ≫
        (gIso W T p).hom.app ((extension R φ i).obj N) := by
  have hc := unmate_paste (moduleJAdj R φ i) (moduleJAdj R φ b)
    (StrictTower.jAdj (R n) i) (StrictTower.jAdj (R n) b)
    (TwoSquare.mk _ _ _ _ (moduleBetaInv R φ a b i p h))
    (TwoSquare.mk _ _ _ _ (StrictTower.betaInv (R n) a b i p h))
    (TwoSquare.mk _ _ _ _ (jIso S T i).inv)
    (TwoSquare.mk _ _ _ _ (jIso V W b).inv)
    (gIso V S a).hom (gIso W T p).hom
    (by
      rw [ordinaryBetaInv_mate, hm, hm]
      rw [strictBetaInv_mate]
      refine NatTrans.ext (funext fun M ↦ ?_)
      simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
        TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id,
        Category.assoc] using ordinaryPull_square_inv R φ n gIso hc a b i p h M)
  have he := congrArg (fun w ↦ w.app N) hc
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using he.symm

/-- Realization preserves the cartesian open factor of the clopen arrow.
Source: Stacks 09AE; Zheng, Construction 4.1
(blueprint: lem-sp-varying-ring-ordinary-cartesian-evaluation).
Proof: transpose the inverse comparisons under the open adjunction for j'.
The ordinary transpose is pullback of the unit for j followed by the inverse
pullback-square comparison. The strict-tower transpose is the same word.
Use the unit normalization of ordinaryOpenComparison and the pullback composition
normalization to identify these words after realization. Equality transports
commute with realization by equality elimination. Injectivity of the open
adjunction Hom equivalence gives the inverse-comparison equation. Cancel the
invertible beta maps to obtain the displayed forward equation. This argument
uses only a cartesian open square, with no clopen section projection. -/
theorem ordinaryCartesianEvaluation (n : ℕ) {V W S T : Scheme.{u}}
    (a : V ⟶ S) (b : V ⟶ W) (i : S ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion b] [IsOpenImmersion i]
    (h : a ≫ i = b ≫ p) (hsq : IsPullback a b i p) :
    OrdinarySquareComparison
      (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n W)
      (EC := ordinaryRealization R φ n S) (ED := ordinaryRealization R φ n T)
      (R₀ := pull R φ a) (P₀ := pull R φ p)
      (K := extension R φ b) (I := extension R φ i)
      (r := StrictTower.G (R n) a) (p := StrictTower.G (R n) p)
      (k := StrictTower.J (R n) b) (i := StrictTower.J (R n) i)
      (ordinaryPullComparison R φ n V S a) (ordinaryPullComparison R φ n W T p)
      (ordinaryOpenComparison R φ n V W b) (ordinaryOpenComparison R φ n S T i)
      (moduleBeta R φ a b i p h hsq).hom
      (StrictTower.beta (R n) a b i p h hsq).hom := by
  exact comparison_of_inverse
    (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n W)
    (EC := ordinaryRealization R φ n S) (ED := ordinaryRealization R φ n T)
    (R₀ := pull R φ a) (P₀ := pull R φ p)
    (K := extension R φ b) (I := extension R φ i)
    (r := StrictTower.G (R n) a) (p := StrictTower.G (R n) p)
    (k := StrictTower.J (R n) b) (i := StrictTower.J (R n) i)
    (ordinaryPullComparison R φ n V S a) (ordinaryPullComparison R φ n W T p)
    (ordinaryOpenComparison R φ n V W b) (ordinaryOpenComparison R φ n S T i)
    (moduleBeta R φ a b i p h hsq) (StrictTower.beta (R n) a b i p h hsq)
    (by
      intro N
      simpa only [moduleBeta, StrictTower.beta, Iso.symm_inv, asIso_hom] using
        ordinaryBeta_inv R φ n (ordinaryPullComparison R φ n)
          (ordinaryOpenComparison R φ n) (ordinaryComparisonNormalization R φ n).1
          (ordinaryOpen_mate R φ n) a b i p h N)

end AlgebraicGeometry.ProEtale.VaryingRing
