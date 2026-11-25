/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryEvaluationComparisons
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Ordinary component evaluation and pullback composition

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 03DI and 09AE.
(blueprint: lem-sp-varying-ring-ordinary-module-composition).
This is the original module-level calculation, separated from the realization
constructions to keep each compilation small.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] ordinaryRealization moduleAlpha moduleGComp moduleJComp
  StrictTower.alpha StrictTower.G StrictTower.J StrictTower.gComp StrictTower.jComp
  Functor.leftAdjoint

private theorem mate_of_unit {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ N : C, G.map (a₁.unit.app N) ≫ β.app (L₁.obj N) =
      a₂.unit.app (G.obj N) ≫ R₂.map (α.app N)) :
    mateEquiv a₁ a₂ α = β := by
  rw [← Equiv.eq_symm_apply]
  refine NatTrans.ext (funext fun N ↦ ?_)
  apply (a₂.homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj] using
    (h N).symm.trans (unit_mateEquiv_symm a₁ a₂ β N)

private abbrev ordinaryLevelAdj (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StrictTower.modulePullback (R n) f ⊣ StrictTower.moduleDirectImage (R n) f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n) (coefficients R X n)
    (StrictTower.constantRingIso (R n) f)

private theorem ordinaryLevelAdj_eq (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryLevelAdj R n f = Scheme.proEtaleRingModuleAdjunction f
      (StrictTower.coefficients (R n) Y) (StrictTower.coefficients (R n) X)
      (StrictTower.constantRingIso (R n) f) := by
  dsimp only [ordinaryLevelAdj, coefficients, StrictTower.coefficients]
  generalize R n = A
  cases A
  rfl

private theorem ordinaryModuleEvalG_mate (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mateEquiv (moduleAdj R φ f) (ordinaryLevelAdj R n f)
      (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv) =
      TwoSquare.mk _ _ _ _ (moduleEvalP R φ f n).hom := by
  apply mate_of_unit
  intro N
  apply (cancel_mono ((StrictTower.moduleDirectImage (R n) f).map
    ((moduleEvalG R φ f n).hom.app N))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (moduleEvalG_existsUnique R φ f n).choose_spec.1 N

private theorem ordinaryModuleEvalP_apply (n : ℕ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (N : Modules R φ X) (U : Y.ProEt)
    (x : ((push R φ f).obj N).val.obj (op (n, U))) :
    ((moduleEvalP R φ f n).hom.app N).val.app (op U) x = x := by
  exact (moduleEvalP_existsUnique R φ f n).choose_spec.1 N U x

private theorem ordinaryLevelPush_map_apply (n : ℕ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) {M N : StrictTower.Modules (R n) X} (a : M ⟶ N) (U : Y.ProEt)
    (x : ((StrictTower.moduleDirectImage (R n) f).obj M).val.obj (op U)) :
    (((StrictTower.moduleDirectImage (R n) f).map a).val.app (op U)) x =
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj U)) x := by
  rfl

private theorem ordinaryEval_map_apply (n : ℕ) (X : Scheme.{u})
    {M N : Modules R φ X} (a : M ⟶ N) (U : X.ProEt)
    (x : M.val.obj (op (n, U))) :
    (((eval R φ X n).map a).val.app (op U)) x = a.val.app (op (n, U)) x := by
  rfl

private theorem ordinaryEval_obj_map_apply (n : ℕ) (X : Scheme.{u})
    (M : Modules R φ X) {U V : X.ProEt} (a : U ⟶ V)
    (x : M.val.obj (op (n, V))) :
    ((eval R φ X n).obj M).val.map a.op x =
      M.val.map (Prod.mkHom (𝟙 n) a).op x := by
  rfl

private theorem ordinaryLevelComp_apply (n : ℕ) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : StrictTower.Modules (R n) X) (U : Z.ProEt)
    (x : ((StrictTower.moduleDirectImage (R n) f ⋙
      StrictTower.moduleDirectImage (R n) g).obj M).val.obj (op U)) :
    ((StrictTower.moduleRComp (R n) f g).hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op x := by
  exact (StrictTower.moduleRComp_existsUnique (R n) f g).choose_spec.1 M U x

private theorem ordinarySystemComp_apply {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules R φ X) (n : ℕ) (U : Z.ProEt)
    (x : ((push R φ f ⋙ push R φ g).obj M).val.obj (op (n, U))) :
    ((modulePComp R φ f g).hom.app M).val.app (op (n, U)) x =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
  exact (modulePComp_existsUnique R φ f g).choose_spec.1 M n U x

attribute [local irreducible] moduleEvalP modulePComp StrictTower.moduleRComp constantSheaf
  WeilConjectures.SemilinearSections.rings

private theorem comparison_of_inverse {C : Type*} [Category C]
    {A B D E : C} (u : B ≅ E) (v : A ≅ D) (a : A ⟶ B) (b : D ⟶ E)
    (h : b ≫ u.inv = v.inv ≫ a) : a ≫ u.hom = v.hom ≫ b := by
  apply (cancel_epi v.inv).1
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

private lemma mateSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Ordinary component evaluation preserves the specified inverse-image compositor.
Source: Zheng, Construction 4.1 and Lemma 4.10
(blueprint: lem-sp-varying-ring-ordinary-module-composition).
Proof: take adjunction mates. The unit normalization identifies the evaluation
mate with the sectionwise identity comparison moduleEvalP. Both pushforward
compositors restrict sections along the same pullback-pasting map, so their
comparison holds on every section. Injectivity of the mate equivalence gives
its inverse-image counterpart; cancellation of the comparison isomorphisms
then gives the displayed orientation. -/
theorem ordinaryModuleEvalG_comp (n : ℕ) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules R φ Z) :
    (eval R φ X n).map ((moduleGComp R φ f g).hom.app N) ≫
        (moduleEvalG R φ f n).hom.app ((pull R φ g).obj N) ≫
        (StrictTower.modulePullback (R n) f).map ((moduleEvalG R φ g n).hom.app N) =
      (moduleEvalG R φ (f ≫ g) n).hom.app N ≫
        (StrictTower.moduleGComp (R n) f g).hom.app ((eval R φ Z n).obj N) := by
  let q := (TwoSquare.mk _ _ _ _ (moduleEvalG R φ g n).inv).vComp
    (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv)
  have hc : q.whiskerRight (StrictTower.moduleGComp (R n) f g).hom =
      (TwoSquare.mk _ _ _ _ (moduleEvalG R φ (f ≫ g) n).inv).whiskerLeft
        (moduleGComp R φ f g).hom := by
    apply mateSquare ((moduleAdj R φ g).comp (moduleAdj R φ f))
      (moduleAdj R φ (f ≫ g))
      ((ordinaryLevelAdj R n g).comp (ordinaryLevelAdj R n f))
      (ordinaryLevelAdj R n (f ≫ g))
    dsimp only [q]
    rw [mateEquiv_hcomp, ordinaryModuleEvalG_mate, ordinaryModuleEvalG_mate,
      ordinaryModuleEvalG_mate]
    have hG : conjugateEquiv ((moduleAdj R φ g).comp (moduleAdj R φ f))
        (moduleAdj R φ (f ≫ g)) (moduleGComp R φ f g).hom =
        (modulePComp R φ f g).hom := by
      simpa only [moduleGComp, Iso.symm_hom] using
        (Adjunction.conjugateEquiv_leftAdjointCompIso_inv
          (moduleAdj R φ g) (moduleAdj R φ f) (moduleAdj R φ (f ≫ g))
          (modulePComp R φ f g))
    have hG' : conjugateEquiv ((ordinaryLevelAdj R n g).comp (ordinaryLevelAdj R n f))
        (ordinaryLevelAdj R n (f ≫ g)) (StrictTower.moduleGComp (R n) f g).hom =
        (StrictTower.moduleRComp (R n) f g).hom := by
      rw [ordinaryLevelAdj_eq, ordinaryLevelAdj_eq, ordinaryLevelAdj_eq]
      exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
    rw [hG, hG']
    refine NatTrans.ext (funext fun M ↦ ?_)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    obtain ⟨U⟩ := U
    let y := ((moduleEvalP R φ g n).hom.app ((push R φ f).obj M)).val.app (op U) x
    let a := ((StrictTower.moduleRComp (R n) f g).hom.app
      ((eval R φ X n).obj M)).val.app (op U)
    let b := ((moduleEvalP R φ (f ≫ g) n).hom.app M).val.app (op U)
    let c := ((eval R φ Z n).map ((modulePComp R φ f g).hom.app M)).val.app (op U)
    have hmap := ordinaryLevelPush_map_apply R n g
      ((moduleEvalP R φ f n).hom.app M) U y
    have hlevel := ordinaryLevelComp_apply R n f g ((eval R φ X n).obj M) U x
    have hsystem := ordinarySystemComp_apply R φ f g M n U x
    have hf := ordinaryModuleEvalP_apply R φ n f M
      ((Scheme.proEtaleBaseChange g).obj U) y
    have hg := ordinaryModuleEvalP_apply R φ n g ((push R φ f).obj M) U x
    have he := ordinaryEval_map_apply R φ n Z
      ((modulePComp R φ f g).hom.app M) U x
    have hfg := ordinaryModuleEvalP_apply R φ n (f ≫ g) M U (c x)
    let v : (Scheme.proEtaleBaseChange (f ≫ g)).obj U ⟶
        (Scheme.proEtaleBaseChange f).obj ((Scheme.proEtaleBaseChange g).obj U) := by
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      exact (MorphismProperty.Over.pullbackComp.{u, u + 1}
        (T := Scheme.{u}) (P := @WeaklyEtale.{u}) (Q := ⊤) f g).hom.app U
    have hv := ordinaryEval_obj_map_apply R φ n X M v x
    exact (congrArg (fun z ↦ a z) hmap).trans
      ((congrArg (fun z ↦ a z) hf).trans
        ((congrArg (fun z ↦ a z) hg).trans
          (hlevel.trans (hv.trans (hsystem.symm.trans (he.symm.trans hfg.symm))))))
  have hm := congrArg (fun z ↦ z.app N) hc
  simp only [q, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at hm
  let u := (moduleEvalG R φ f n).app ((pull R φ g).obj N) ≪≫
    (StrictTower.modulePullback (R n) f).mapIso ((moduleEvalG R φ g n).app N)
  let v := (moduleEvalG R φ (f ≫ g) n).app N
  exact comparison_of_inverse u v
    ((eval R φ X n).map ((moduleGComp R φ f g).hom.app N))
    ((StrictTower.moduleGComp (R n) f g).hom.app ((eval R φ Z n).obj N)) hm

end AlgebraicGeometry.ProEtale.VaryingRing
