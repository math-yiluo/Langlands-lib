/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore

import Mathlib.Util.AliasIn
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import all WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # Existing evaluation constructions for semilinear proper/open mates

This part of the intrinsic coefficient API is separated to keep each file within
the compilation limit. The original constructions and their properties are retained.

## References

* Zheng 4.1 and 4.10
* Stacks 03CZ and 03D7
* Stacks 03EK
* Zheng 4.10
* Stacks 03DI and the ring-sheaf change adjunction
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 32
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
section ProofEnvironment
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf Functor.mapDerivedCategoryNatIso
  HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
attribute [local irreducible] SemilinearSections.systemRing
  coefficientMap VaryingRing.ringMap alpha gamma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluation at n followed by the actual constant strict diagram. This construction
retains the input module, without choices of maps or coefficient lifts. -/
abbrev levelTower (n : ℕ) (X : Scheme.{u}) :
    Modules C τ X ⥤ StrictTower.Towers (C n) X :=
  SemilinearSections.evaluation.{u + 1, u, u + 1}
    (ProEt.topology X) (coefficients C X) (transition C τ X) n ⋙
      Functor.const ℕᵒᵖ

/-- Exact localization of evaluation followed by a constant diagram. Evaluation at
any tower index recovers the actual n-th module, with its C_n action. -/
abbrev E (n : ℕ) (X : Scheme.{u}) := (levelTower C τ n X).mapDerivedCategory
section Evaluation
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible]
  VaryingRing.coefficientTransition StrictTower.G StrictTower.R P R
variable (n : ℕ)

attribute [local irreducible] proEtaleRingDirectImageMap proEtaleConstantDirectImageMap
attribute [local irreducible] VaryingRing.moduleEvalP
attribute [local irreducible] StrictTower.constantRingIso

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Use the canonical comparison and derive its inverse formula from the isomorphism law.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem level_push_evaluation_canonical {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) (hF : F = VaryingRing.push C τ f) :
    ∃ d : F ⋙ VaryingRing.eval C τ Y n ≅
        VaryingRing.eval C τ X n ⋙ StrictTower.moduleDirectImage (C n) f,
      (∀ (M : Modules C τ X) (U : Y.ProEt),
        HEq (fun x ↦ (d.hom.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) ∧
      (∀ (M : Modules C τ X) (U : Y.ProEt),
        HEq (fun x ↦ (d.inv.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) ∧
      d = eqToIso (congrArg (fun T ↦ T ⋙ VaryingRing.eval C τ Y n) hF) ≪≫
        VaryingRing.moduleEvalP C τ f n := by
  subst F
  let d := VaryingRing.moduleEvalP C τ f n
  have hd (M : Modules C τ X) (U : Y.ProEt)
      (x : M.val.obj (op (n, (proEtaleBaseChange f).obj U))) :
      (d.hom.app M).val.app (op U) x = x := by
    dsimp only [d]
    unfold VaryingRing.moduleEvalP
    exact (VaryingRing.moduleEvalP_existsUnique C τ f n).choose_spec.1 M U x
  refine ⟨d, fun M U ↦ heq_of_eq (funext (hd M U)), ?_, ?_⟩
  · intro M U
    apply heq_of_eq
    funext x
    have h := congrArg (fun t ↦ t.val.app (op U) x) (d.inv_hom_id_app M)
    change (d.hom.app M).val.app (op U) ((d.inv.app M).val.app (op U) x) = x at h
    exact (hd M U _).symm.trans h
  · simp only [d, eqToIso_refl, Iso.refl_trans]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem level_push_evaluation_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) (hF : F = VaryingRing.push C τ f) :
    ∃ d : F ⋙ VaryingRing.eval C τ Y n ≅
        VaryingRing.eval C τ X n ⋙ StrictTower.moduleDirectImage (C n) f,
      (∀ (M : Modules C τ X) (U : Y.ProEt),
        HEq (fun x ↦ (d.hom.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) ∧
      (∀ (M : Modules C τ X) (U : Y.ProEt),
        HEq (fun x ↦ (d.inv.app M).val.app (op U) x)
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) := by
  obtain ⟨d, hd, hi, _⟩ := level_push_evaluation_canonical C τ n f F hF
  exact ⟨d, hd, hi⟩

attribute [local irreducible] SheafOfModules.pushforward

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem eval_constant_diagram_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y)
    (d : F ⋙ VaryingRing.eval C τ Y n ≅
      VaryingRing.eval C τ X n ⋙ StrictTower.moduleDirectImage (C n) f)
    (hi : ∀ (M : Modules C τ X) (U : Y.ProEt),
      HEq (fun x ↦ (d.inv.app M).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x))
    (e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      F ⋙ levelTower C τ n Y)
    (he : ∀ (M : Modules C τ X) (m : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op m)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    e = (constant_diagram_square F (VaryingRing.eval C τ Y n)
      (VaryingRing.eval C τ X n) (StrictTower.moduleDirectImage (C n) f) d).symm := by
  apply tower_iso_ext_sections
  intro M m U
  exact (he M m.unop U.unop).trans (hi M U.unop).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- The uniqueness proof compares the section carriers of both composite functors.
/-- Direct image and evaluation commute by the identity on component sections. -/
theorem evalPushOrdinary_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      push C τ f ⋙ levelTower C τ n Y,
      ∀ (M : Modules C τ X) (m : ℕ) (U : Y.ProEt),
        HEq (fun x ↦ ((((e.hom.app M).app (op m)).val.app (op U)) x))
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x) := by
  obtain ⟨d, _, hd, _⟩ := level_push_evaluation_canonical C τ n f (push C τ f)
    (push_eq C τ f)
  let e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      push C τ f ⋙ levelTower C τ n Y :=
    (constant_diagram_square (push C τ f) (VaryingRing.eval C τ Y n)
      (VaryingRing.eval C τ X n) (StrictTower.moduleDirectImage (C n) f) d).symm
  refine ⟨e, ?_, ?_⟩
  · intro M m U
    change HEq (fun x ↦ (d.inv.app M).val.app (op U) x)
      (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)
    exact hd M U
  · intro e' he'
    exact eval_constant_diagram_eq C τ n f (push C τ f) d hd e' he'

/-- The ordinary inverse-image scalar comparison is the transpose of the uniquely
section-normalized direct-image comparison. -/
def evalPullInv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    levelTower C τ n Y ⋙ StrictTower.towerPullback (C n) f ⟶
      pull C τ f ⋙ levelTower C τ n X :=
  (mateEquiv (ordinaryAdj C τ f)
    ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
      (StrictTower.coefficients (C n) X)
      (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm
    (evalPushOrdinary_existsUnique C τ n f).choose.inv

attribute [local irreducible] constant_diagram_square SemilinearSections.evaluation

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Compare normalized component isomorphisms before lifting the adjunction unit.
private theorem eval_pull_mate_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      VaryingRing.push C τ f ⋙ levelTower C τ n Y)
    (he : ∀ (M : Modules C τ X) (m : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op m)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    ((mateEquiv (VaryingRing.moduleAdj C τ f)
      ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X)
        (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm e.inv) =
      (constant_diagram_square (VaryingRing.pull C τ f)
        (VaryingRing.eval C τ X n) (VaryingRing.eval C τ Y n)
        (StrictTower.modulePullback (C n) f) (VaryingRing.moduleEvalG C τ f n)).inv := by
  obtain ⟨d, hd, hi, hcanonical⟩ := level_push_evaluation_canonical C τ n f
    (VaryingRing.push C τ f) rfl
  have hd' : d = VaryingRing.moduleEvalP C τ f n := by
    simpa only [eqToIso_refl, Iso.refl_trans] using hcanonical
  obtain ⟨g, hg, _⟩ := VaryingRing.moduleEvalG_existsUnique C τ f n
  let D := constant_diagram_square (VaryingRing.push C τ f)
    (VaryingRing.eval C τ Y n) (VaryingRing.eval C τ X n)
    (StrictTower.moduleDirectImage (C n) f) d
  let G := constant_diagram_square (VaryingRing.pull C τ f)
    (VaryingRing.eval C τ X n) (VaryingRing.eval C τ Y n)
    (StrictTower.modulePullback (C n) f) g
  have he' : e = D.symm :=
    eval_constant_diagram_eq C τ n f (VaryingRing.push C τ f) d hi e he
  have hm : mateEquiv (VaryingRing.moduleAdj C τ f)
      ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X)
        (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ) G.inv = D.hom := by
    apply constant_diagram_mate (VaryingRing.moduleAdj C τ f)
      (proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X) (StrictTower.constantRingIso (C n) f))
      (VaryingRing.eval C τ Y n) (VaryingRing.eval C τ X n) g d
    intro M
    rw [hd']
    exact hg M
  rw [he']
  change ((mateEquiv (VaryingRing.moduleAdj C τ f)
    ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
      (StrictTower.coefficients (C n) X)
      (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm D.hom) = _
  rw [← hm]
  erw [Equiv.symm_apply_apply]
  have hg' : g = VaryingRing.moduleEvalG C τ f n := by
    apply (VaryingRing.moduleEvalG_existsUnique C τ f n).choose_spec.2
    exact hg
  dsimp only [G]
  rw [hg']

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem eval_pull_mate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      F ⋙ levelTower C τ n Y)
    (he : ∀ (M : Modules C τ X) (m : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op m)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    IsIso ((mateEquiv (Adjunction.ofIsRightAdjoint F)
      ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X)
        (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm e.inv) := by
  subst F
  change IsIso (((mateEquiv (VaryingRing.moduleAdj C τ f)
    ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
      (StrictTower.coefficients (C n) X)
      (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm e.inv))
  rw [eval_pull_mate_normalization C τ n f e he]
  exact (constant_diagram_square (VaryingRing.pull C τ f)
    (VaryingRing.eval C τ X n) (VaryingRing.eval C τ Y n)
    (StrictTower.modulePullback (C n) f) (VaryingRing.moduleEvalG C τ f n)).isIso_inv

/-- The identified-coefficient inverse-image scalar comparison is invertible. -/
theorem evalPullInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (evalPullInv C τ n f) := by
  exact eval_pull_mate_isIso C τ n f (push C τ f) (push_eq C τ f)
    (evalPushOrdinary_existsUnique C τ n f).choose
    (evalPushOrdinary_existsUnique C τ n f).choose_spec.1

/-- The canonical evaluation inverse-image comparison after exact localization. -/
def evalP {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P C τ f ⋙ E C τ n X ≅ E C τ n Y ⋙ StrictTower.G (C n) f :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
  Functor.mapDerivedCategoryNatIso
    (@asIso _ _ _ _ (evalPullInv C τ n f) (evalPullInv_isIso C τ n f)).symm ≪≫
  (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The direct-image comparison is the actual derived mate of evalP inverse. -/
def evalR {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R C τ f ⋙ E C τ n Y ⟶ E C τ n X ⋙ StrictTower.R (C n) f :=
  mateEquiv (adj C τ f) (StrictTower.adj (C n) f) (evalP C τ n f).inv

section EvaluationCategoricalProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
  CategoryTheory.exactLocalizationDerivedAdjunction

private theorem mate_pasted_isIso
    {A B D F H I : Type*} [Category A] [Category B] [Category D]
    [Category F] [Category H] [Category I]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {L₃ : H ⥤ I} {R₃ : I ⥤ H}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {T₁ : A ⥤ D} {B₁ : B ⥤ F} {T₂ : D ⥤ H} {B₂ : F ⥤ I}
    {T : A ⥤ H} {S : B ⥤ I}
    (w₁ : TwoSquare T₁ L₁ L₂ B₁) (w₂ : TwoSquare T₂ L₂ L₃ B₂)
    (w : TwoSquare T L₁ L₃ S) (a : T ≅ T₁ ⋙ T₂) (b : S ≅ B₁ ⋙ B₂)
    (h : Functor.whiskerRight a.hom L₃ ≫ (w₁.hComp w₂) =
      w ≫ Functor.whiskerLeft L₁ b.hom)
    [IsIso (mateEquiv a₁ a₂ w₁)]
    [IsIso (mateEquiv a₂ a₃ w₂)] :
    IsIso (mateEquiv a₁ a₃ w) := by
  have hw : w = ((w₁.hComp w₂).whiskerTop a.hom).whiskerBottom b.inv := by
    ext X
    have ht := NatTrans.congr_app h X
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ht
    apply (cancel_mono (b.hom.app (L₁.obj X))).mp
    simpa [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, Category.assoc] using ht.symm
  rw [hw, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp a₁ a₂ a₃]
  dsimp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp]
  infer_instance

private theorem inverse_mate_change_isIso
    {A B D F : Type*} [Category A] [Category B] [Category D] [Category F]
    {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : D ⥤ F} {R₂ : F ⥤ D}
    {G : A ⥤ D} {H : B ⥤ F}
    (a₁ : L₁ ⊣ R₁) (b₁ : L₁' ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₂ : L₂' ⊣ R₂)
    (w : TwoSquare R₁ H G R₂)
    [IsIso ((mateEquiv b₁ b₂).symm w)] :
    IsIso ((mateEquiv a₁ a₂).symm w) := by
  have hw : (mateEquiv a₁ a₂).symm w = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G (a₂.leftAdjointUniq b₂).hom ≫
        ((mateEquiv b₁ b₂).symm w) ≫
          Functor.whiskerRight (a₁.leftAdjointUniq b₁).inv H) := by
    apply (mateEquiv a₁ a₂).injective
    rw [Equiv.apply_symm_apply, mateEquiv_leftAdjointUniq, Equiv.apply_symm_apply]
  rw [hw]
  dsimp only [TwoSquare.mk]
  apply IsIso.comp_isIso'
  · exact (Functor.isoWhiskerLeft G (a₂.leftAdjointUniq b₂)).isIso_hom
  · apply IsIso.comp_isIso'
    · infer_instance
    · exact (Functor.isoWhiskerRight (a₁.leftAdjointUniq b₁).symm H).isIso_hom

private theorem inverse_mate_pasted_isIso
    {A B D F H I : Type*} [Category A] [Category B] [Category D]
    [Category F] [Category H] [Category I]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {L₃ : H ⥤ I} {R₃ : I ⥤ H}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {T₁ : A ⥤ D} {B₁ : B ⥤ F} {T₂ : D ⥤ H} {B₂ : F ⥤ I}
    {T : A ⥤ H} {S : B ⥤ I}
    (w₁ : TwoSquare R₁ B₁ T₁ R₂) (w₂ : TwoSquare R₂ B₂ T₂ R₃)
    (w : TwoSquare R₁ S T R₃) (a : T ≅ T₁ ⋙ T₂) (b : S ≅ B₁ ⋙ B₂)
    (h : Functor.whiskerLeft R₁ a.hom ≫ (w₁.vComp w₂) =
      w ≫ Functor.whiskerRight b.hom R₃)
    [IsIso ((mateEquiv a₁ a₂).symm w₁)]
    [IsIso ((mateEquiv a₂ a₃).symm w₂)] :
    IsIso ((mateEquiv a₁ a₃).symm w) := by
  let v := ((mateEquiv a₁ a₂).symm w₁).hComp ((mateEquiv a₂ a₃).symm w₂)
  have hv : mateEquiv a₁ a₃ v = w₁.vComp w₂ := by
    dsimp only [v]
    rw [mateEquiv_vcomp a₁ a₂ a₃, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hw : mateEquiv a₁ a₃ ((v.whiskerTop a.hom).whiskerBottom b.inv) = w := by
    rw [mateEquiv_whiskerTop_whiskerBottom, hv]
    ext X
    have ht := NatTrans.congr_app h X
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ht
    apply (cancel_mono (R₃.map (b.hom.app X))).mp
    simpa [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, Category.assoc,
      ← Functor.map_comp] using ht
  rw [← hw, Equiv.symm_apply_apply]
  dsimp only [v, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    TwoSquare.mk]
  repeat' apply IsIso.comp_isIso'
  all_goals first
    | exact Functor.isIso_whiskerLeft T₁ ((mateEquiv a₂ a₃).symm w₂)
    | exact Functor.isIso_whiskerRight ((mateEquiv a₁ a₂).symm w₁) B₂
    | infer_instance

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe v h w

open SheafOfModules.OpenTensorNormalization in
private theorem exact_hom_fac
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    (exactDerivedAdjunction a).homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app L := by
  have hu : (exactDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    simp only [exactDerivedAdjunction, Adjunction.localization_unit_app]
    rfl
  rw [Adjunction.homEquiv_unit, hu, G.mapDerivedCategory.map_comp]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp]
  have hn := G.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

open SheafOfModules.OpenTensorNormalization in
private theorem exact_inverse_mate_isIso
    {A B D F : Type v} [Category.{h} A] [Category.{h} B]
    [Category.{h} D] [Category.{h} F]
    [Abelian A] [Abelian B] [Abelian D] [Abelian F]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} D] [HasDerivedCategory.{w} F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {G : A ⥤ D} {H : B ⥤ F}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ⋙ G ≅ H ⋙ R₂)
    [IsIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom))] :
    IsIso ((mateEquiv (exactDerivedAdjunction a₁) (exactDerivedAdjunction a₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)) := by
  have := (CategoryTheory.exact_localization_inverse_mate a₁ a₂ d).1
  exact inverse_mate_change_isIso (exactDerivedAdjunction a₁)
    (CategoryTheory.exactLocalizationDerivedAdjunction a₁) (exactDerivedAdjunction a₂)
    (CategoryTheory.exactLocalizationDerivedAdjunction a₂)
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)

private theorem constant_open_inverse_mate_isIso (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : (StrictTower.moduleJ A j).mapDerivedCategory ⊣
      (StrictTower.modulePullback A j).mapDerivedCategory)
    (b : (StrictTower.towerJ A j).mapDerivedCategory ⊣
      (StrictTower.towerPullback A j).mapDerivedCategory) :
    IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso
        (Functor.compConstIso ℕᵒᵖ (StrictTower.modulePullback A j))).hom)) := by
  let c := StrictTower.moduleJAdj A j
  let d := Functor.compConstIso ℕᵒᵖ (StrictTower.modulePullback A j)
  have hm : (mateEquiv c (c.whiskerRight ℕᵒᵖ)).symm (TwoSquare.mk _ _ _ _ d.hom) =
      TwoSquare.mk _ _ _ _ (Functor.compConstIso ℕᵒᵖ (StrictTower.moduleJ A j)).inv := by
    apply (mateEquiv c (c.whiskerRight ℕᵒᵖ)).injective
    rw [Equiv.apply_symm_apply]
    exact (StrictTower.ConstantNormalization.const_mate _ _ c).symm
  have : IsIso ((mateEquiv c (c.whiskerRight ℕᵒᵖ)).symm
      (TwoSquare.mk _ _ _ _ d.hom)) := by
    rw [hm]
    exact (Functor.compConstIso ℕᵒᵖ (StrictTower.moduleJ A j)).isIso_inv
  have := exact_inverse_mate_isIso c (c.whiskerRight ℕᵒᵖ) d
  exact inverse_mate_change_isIso a
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction c) b
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (c.whiskerRight ℕᵒᵖ))
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)

end EvaluationCategoricalProof

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
  CategoryTheory.exactLocalizationDerivedAdjunction

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Normalize the chosen adjoints before comparing the exact derived composition squares.
private theorem eval_derived_mate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint] [F.Additive]
    [F.leftAdjoint.Additive] [PreservesFiniteLimits F.leftAdjoint]
    [PreservesFiniteColimits F.leftAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : levelTower C τ n X ⋙ StrictTower.towerDirectImage (C n) f ≅
      F ⋙ levelTower C τ n Y)
    (he : ∀ (M : Modules C τ X) (m : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op m)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x))
    (s : levelTower C τ n Y ⋙ StrictTower.towerPullback (C n) f ≅
      F.leftAdjoint ⋙ levelTower C τ n X)
    (hs : s.hom = (mateEquiv (Adjunction.ofIsRightAdjoint F)
      ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X)
        (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm e.inv) :
    IsIso (mateEquiv
      (Adjunction.ofIsRightAdjoint F).mapDerivedCategoryRightDerivedAdjunction
      (StrictTower.adj (C n) f) (Functor.mapDerivedCategorySquareIso s).hom) := by
  subst F
  let G := constant_diagram_square (VaryingRing.pull C τ f)
    (VaryingRing.eval C τ X n) (VaryingRing.eval C τ Y n)
    (StrictTower.modulePullback (C n) f) (VaryingRing.moduleEvalG C τ f n)
  have hs' : s = G.symm := by
    apply Iso.ext
    rw [hs]
    exact eval_pull_mate_normalization C τ n f e he
  rw [hs']
  clear! s e
  let q := (Functor.compConstIso ℕᵒᵖ (StrictTower.modulePullback (C n) f)).symm
  let w₁ := TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (VaryingRing.moduleEvalG C τ f n).symm).hom
  let w₂ := TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso q).hom
  have : IsIso (mateEquiv (VaryingRing.adj C τ f)
      (VaryingRing.levelAdj C f n) w₁) := by
    dsimp only [w₁]
    rw [Functor.square_symm_hom]
    exact VaryingRing.evalPMate_isIso C τ f n
  have : IsIso (mateEquiv (VaryingRing.levelAdj C f n)
      (StrictTower.adj (C n) f) w₂) := by
    change IsIso (mateEquiv
      (proEtaleRingDerivedAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X) (StrictTower.constantRingIso (C n) f))
      (StrictTower.adj (C n) f)
      (TwoSquare.mk _ _ _ _
        (StrictTower.ConstantNormalization.deltaPull (C n) f).hom))
    rw [← StrictTower.ConstantNormalization.chi_mate]
    exact (StrictTower.ConstantNormalization.chi (C n) f).isIso_hom
  exact mate_pasted_isIso (VaryingRing.adj C τ f) (VaryingRing.levelAdj C f n)
    (StrictTower.adj (C n) f) w₁ w₂ (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso G.symm).hom)
    (Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (derived_constant_square_comp (VaryingRing.pull C τ f)
      (VaryingRing.eval C τ X n) (VaryingRing.eval C τ Y n)
      (StrictTower.modulePullback (C n) f) (VaryingRing.moduleEvalG C τ f n))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Identify the normalized ordinary square before taking the two exact open mates.
private theorem eval_open_mate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (F : VaryingRing.Modules C τ X ⥤ VaryingRing.Modules C τ Y) [F.IsRightAdjoint] [F.Additive]
    [F.leftAdjoint.Additive] [PreservesFiniteLimits F.leftAdjoint]
    [PreservesFiniteColimits F.leftAdjoint]
    [F.leftAdjoint.IsRightAdjoint] [F.leftAdjoint.leftAdjoint.Additive]
    [PreservesFiniteLimits F.leftAdjoint.leftAdjoint]
    [PreservesFiniteColimits F.leftAdjoint.leftAdjoint]
    (ao : F.leftAdjoint.leftAdjoint.mapDerivedCategory ⊣ F.leftAdjoint.mapDerivedCategory)
    (hF : F = VaryingRing.push C τ f)
    (e : (VaryingRing.eval C τ X n ⋙ Functor.const ℕᵒᵖ) ⋙ StrictTower.towerDirectImage (C n) f ≅
      F ⋙ (VaryingRing.eval C τ Y n ⋙ Functor.const ℕᵒᵖ))
    (he : ∀ (M : VaryingRing.Modules C τ X) (m : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op m)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x))
    (s : (VaryingRing.eval C τ Y n ⋙ Functor.const ℕᵒᵖ) ⋙ StrictTower.towerPullback (C n) f ≅
      F.leftAdjoint ⋙ (VaryingRing.eval C τ X n ⋙ Functor.const ℕᵒᵖ))
    (hs : s.hom = (mateEquiv (Adjunction.ofIsRightAdjoint F)
      ((proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
        (StrictTower.coefficients (C n) X)
        (StrictTower.constantRingIso (C n) f)).whiskerRight ℕᵒᵖ)).symm e.inv) :
    IsIso ((mateEquiv ao (StrictTower.jAdj (C n) f)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).inv)) := by
  subst F
  let G := constant_diagram_square (VaryingRing.pull C τ f)
    (VaryingRing.eval C τ X n) (VaryingRing.eval C τ Y n)
    (StrictTower.modulePullback (C n) f) (VaryingRing.moduleEvalG C τ f n)
  have hs' : s = G.symm := by
    apply Iso.ext
    rw [hs]
    exact eval_pull_mate_normalization C τ n f e he
  rw [hs']
  clear! s e
  have hG : (Functor.mapDerivedCategorySquareIso G.symm).inv =
      (Functor.mapDerivedCategorySquareIso G).hom := by
    exact (Functor.square_symm_hom G.symm).symm
  rw [hG]
  let q := Functor.compConstIso ℕᵒᵖ (StrictTower.modulePullback (C n) f)
  let w₁ := TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (VaryingRing.moduleEvalG C τ f n)).hom
  let w₂ := TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso q).hom
  have : IsIso ((mateEquiv (VaryingRing.jAdj C τ f)
      (VaryingRing.levelJAdj C f n)).symm w₁) := by
    exact VaryingRing.evalJInv_isIso C τ f n
  have : IsIso ((mateEquiv ao (VaryingRing.levelJAdj C f n)).symm w₁) :=
    inverse_mate_change_isIso ao (VaryingRing.jAdj C τ f)
      (VaryingRing.levelJAdj C f n) (VaryingRing.levelJAdj C f n) w₁
  have : IsIso ((mateEquiv (VaryingRing.levelJAdj C f n)
      (StrictTower.jAdj (C n) f)).symm w₂) := by
    exact constant_open_inverse_mate_isIso (C n) f
      (VaryingRing.levelJAdj C f n) (StrictTower.jAdj (C n) f)
  exact inverse_mate_pasted_isIso ao (VaryingRing.levelJAdj C f n)
    (StrictTower.jAdj (C n) f) w₁ w₂ (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso G).hom)
    (Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (derived_constant_square_inverse (VaryingRing.pull C τ f)
      (VaryingRing.eval C τ X n) (VaryingRing.eval C τ Y n)
      (StrictTower.modulePullback (C n) f) (VaryingRing.moduleEvalG C τ f n))

/-- The specified derived direct-image mate is invertible. -/
theorem evalR_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (evalR C τ n f) := by
  let s := @asIso _ _ _ _ (evalPullInv C τ n f) (evalPullInv_isIso C τ n f)
  have hp : (evalP C τ n f).inv = (Functor.mapDerivedCategorySquareIso s).hom := by
    simp only [evalP, s, Functor.mapDerivedCategorySquareIso, Iso.trans_inv,
      Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, derived_iso_symm_inv, Category.assoc]
  unfold evalR
  rw [hp]
  exact eval_derived_mate_isIso C τ n f (push C τ f) (push_eq C τ f)
    (evalPushOrdinary_existsUnique C τ n f).choose
    (evalPushOrdinary_existsUnique C τ n f).choose_spec.1 s rfl

/-- The open scalar comparison is fixed by the open-adjunction transpose of evalP. -/
def evalJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    E C τ n U ⋙ StrictTower.J (C n) j ⟶ J C τ j ⋙ E C τ n X :=
  (mateEquiv (jAdj C τ j) (StrictTower.jAdj (C n) j)).symm (evalP C τ n j).hom

/-- Open extension commutes with evaluation under its ordinary section units. -/
theorem evalJInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (evalJInv C τ n j) := by
  let s := @asIso _ _ _ _ (evalPullInv C τ n j) (evalPullInv_isIso C τ n j)
  have hp : (evalP C τ n j).hom = (Functor.mapDerivedCategorySquareIso s).inv := by
    exact Functor.square_symm_hom s
  unfold evalJInv
  rw [hp]
  exact @eval_open_mate_isIso C τ n U X j inferInstance (push C τ j)
    (push_isRightAdjoint C τ j) (push_additive C τ j) (pull_additive C τ j)
    (pull_limits C τ j) (pull_colimits C τ j) (openPull_isRightAdjoint C τ j)
    (extension_additive C τ j) (extension_limits C τ j) (extension_colimits C τ j)
    (jAdj C τ j) (push_eq C τ j)
    (evalPushOrdinary_existsUnique C τ n j).choose
    (evalPushOrdinary_existsUnique C τ n j).choose_spec.1 s rfl

/-- The invertible, open-unit-normalized evaluation comparison. -/
def evalJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j ⋙ E C τ n X ≅ E C τ n U ⋙ StrictTower.J (C n) j :=
  (@asIso _ _ _ _ (evalJInv C τ n j) (evalJInv_isIso C τ n j)).symm

end Evaluation

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace SemilinearProperOpenEvaluationAliases
private alias level_push_evaluation_normalized :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.level_push_evaluation_normalized
private alias inverse_mate_change_isIso :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.inverse_mate_change_isIso
private alias inverse_mate_pasted_isIso :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.inverse_mate_pasted_isIso
private alias exact_hom_fac :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.exact_hom_fac
private alias exact_inverse_mate_isIso :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.exact_inverse_mate_isIso
end SemilinearProperOpenEvaluationAliases

end ProofEnvironment
