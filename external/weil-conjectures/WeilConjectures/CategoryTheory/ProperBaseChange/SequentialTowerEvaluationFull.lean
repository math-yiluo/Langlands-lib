/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Lifting compatible derived maps of sequential towers

Source: Stacks Project, Injectives, Tag 079P, and Derived Categories, Tag 070I;
sequential homotopy correction as written in the DAG proof
(blueprint: lem-weil-pbc-sequential-tower-evaluation-full).

The natural-number index `n` denotes the positive level `n + 1` of the source.
-/

@[expose] public section

set_option linter.privateModule false
universe u wA wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Surjectivity of localization on maps into a K-injective target. -/
private theorem tower_chainMap_rep
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P J : CochainComplex A ℤ) [J.IsKInjective]
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj J) :
    ∃ a : P ⟶ J, DerivedCategory.Q.map a = f := by
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨a, ha⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj P) J).surjective
      (e.hom.app P ≫ f ≫ e.inv.app J)
  obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective a
  refine ⟨a, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality a
  rw [ha] at h
  simpa [e] using h.symm

/-- Equality after localization into a K-injective target gives a chain homotopy. -/
private theorem tower_homotopy_of_Q_eq
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P J : CochainComplex A ℤ} [J.IsKInjective]
    (a b : P ⟶ J) (h : DerivedCategory.Q.map a = DerivedCategory.Q.map b) :
    Nonempty (Homotopy a b) := by
  apply Nonempty.intro
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ J).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app J)).1
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]

/-- Lift a commutation homotopy through degreewise sections and subtract its boundary. -/
private theorem tower_correct_map
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P J K : CochainComplex A ℤ}
    (a : P ⟶ J) (b : P ⟶ K) (t : J ⟶ K)
    (s : ∀ i, K.X i ⟶ J.X i) (hs : ∀ i, s i ≫ t.f i = 𝟙 _)
    (H : Homotopy (a ≫ t) b) :
    ∃ c : P ⟶ J, c ≫ t = b ∧ DerivedCategory.Q.map c = DerivedCategory.Q.map a := by
  let l := fun i j ↦ H.hom i j ≫ s j
  let d := Homotopy.nullHomotopicMap l
  have hd : d ≫ t = a ≫ t - b := by
    rw [Homotopy.nullHomotopicMap_comp]
    have he : (fun i j ↦ l i j ≫ t.f j) = H.hom := by
      funext i j
      dsimp [l]
      rw [Category.assoc, hs, Category.comp_id]
    rw [he]
    ext i
    simpa [Homotopy.nullHomotopicMap] using
      (eq_sub_iff_add_eq.mpr (H.comm i).symm)
  refine ⟨a - d, ?_, ?_⟩
  · rw [Preadditive.sub_comp, hd]
    abel
  · have hzero : DerivedCategory.Q.map d = 0 := by
      simpa using DerivedCategory.Q_map_eq_of_homotopy A
        (Homotopy.nullHomotopy l (fun i j hij ↦ by simp [l, H.zero i j hij]))
    simp [hzero]

/-- Extend the finite staircase map into an injective tower by one level. -/
private theorem injective_tower_transition_split
    {A : Type*} [Category A] [Abelian A]
    (T : ℕᵒᵖ ⥤ A) [Injective T]
    (n : ℕ) : IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op) := by
  classical
  let k := (homOfLE (Nat.le_succ n)).op
  let M := T.obj (op n)
  let L := (evaluationLeftAdjoint A (op n)).obj M
  let L' := (evaluationLeftAdjoint A (op (n + 1))).obj M
  let i : L ⟶ L' :=
    { app := fun m ↦ Sigma.desc fun g ↦ Sigma.ι (fun _ ↦ M) (k ≫ g)
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, L', evaluationLeftAdjoint, Category.assoc] }
  have (m : ℕᵒᵖ) : Mono (i.app m) := by
    let r : L'.obj m ⟶ L.obj m := Sigma.desc fun _ ↦
      if h : Nonempty (op n ⟶ m) then Sigma.ι (fun _ ↦ M) h.some else 0
    have hr : i.app m ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro g
      simp only [i, r, colimit.ι_desc_assoc, Cofan.mk_ι_app,
        dite_eq_left (show Nonempty (op n ⟶ m) from ⟨g⟩), colimit.ι_desc]
      exact (congrArg (Sigma.ι (fun _ : op n ⟶ m ↦ M))
        (Subsingleton.elim _ g)).trans (Category.comp_id _).symm
    exact (IsSplitMono.mk' ⟨r, hr⟩).mono
  have : Mono i := NatTrans.mono_of_mono_app i
  let a : L ⟶ T :=
    { app := fun m ↦ Sigma.desc fun g ↦ T.map g
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, evaluationLeftAdjoint, Functor.map_comp] }
  let b := Injective.factorThru a i
  have hb : i ≫ b = a := Injective.comp_factorThru a i
  refine IsSplitEpi.mk' ⟨Sigma.ι (fun _ ↦ M) (𝟙 (op (n + 1))) ≫
    b.app (op (n + 1)), ?_⟩
  rw [Category.assoc, ← b.naturality k, ← Category.assoc]
  have hn := congrArg (fun f : L ⟶ T ↦
    Sigma.ι (fun _ ↦ M) (𝟙 (op n)) ≫ f.app (op n)) hb
  simpa [L', evaluationLeftAdjoint, i, a] using hn

/-- Recursively correct chain representatives and assemble the resulting strict tower map. -/
private theorem tower_strictify
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hK : ∀ n : ℕ, CochainComplex.IsKInjective (J.asFunctor.obj (op n)))
    (hS : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((J.X i).map (homOfLE (Nat.le_succ n)).op))
    (f : ∀ n : ℕ, DerivedCategory.Q.obj (P.asFunctor.obj (op n)) ⟶
      DerivedCategory.Q.obj (J.asFunctor.obj (op n)))
    (hf : ∀ n, f (n + 1) ≫ DerivedCategory.Q.map
        (J.asFunctor.map (homOfLE (Nat.le_succ n)).op) =
      DerivedCategory.Q.map (P.asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫ f n) :
    ∃ b : P ⟶ J, ∀ n : ℕ, DerivedCategory.Q.map
      ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).map b) = f n := by
  classical
  have : ∀ n : ℕ, CochainComplex.IsKInjective (J.asFunctor.obj (op n)) := hK
  have : ∀ (n : ℕ) (i : ℤ),
      IsSplitEpi ((J.X i).map (homOfLE (Nat.le_succ n)).op) := hS
  let L (n : ℕ) := {a : P.asFunctor.obj (op n) ⟶ J.asFunctor.obj (op n) //
    DerivedCategory.Q.map a = f n}
  have inhabited (n : ℕ) : Nonempty (L n) := by
    obtain ⟨a, ha⟩ := tower_chainMap_rep _ _ (f n)
    exact ⟨⟨a, ha⟩⟩
  have extend (n : ℕ) (b : L n) :
      ∃ c : L (n + 1), c.val ≫ J.asFunctor.map (homOfLE (Nat.le_succ n)).op =
        P.asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ b.val := by
    let a := (inhabited (n + 1)).some
    have he : DerivedCategory.Q.map
        (a.val ≫ J.asFunctor.map (homOfLE (Nat.le_succ n)).op) =
        DerivedCategory.Q.map
          (P.asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ b.val) := by
      simp only [Functor.map_comp, a.property, b.property, hf]
    obtain ⟨H⟩ := tower_homotopy_of_Q_eq _ _ he
    obtain ⟨c, hc, hc'⟩ := tower_correct_map a.val
      (P.asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ b.val)
      (J.asFunctor.map (homOfLE (Nat.le_succ n)).op)
      (fun i ↦ section_ ((J.X i).map (homOfLE (Nat.le_succ n)).op))
      (fun i ↦ IsSplitEpi.id _) H
    exact ⟨⟨c, hc'.trans a.property⟩, hc⟩
  let next (n : ℕ) (b : L n) : L (n + 1) := (extend n b).choose
  let lifts : ∀ n, L n := fun n ↦ Nat.rec (inhabited 0).some next n
  have compat (n : ℕ) :
      P.asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ (lifts n).val =
      (lifts (n + 1)).val ≫ J.asFunctor.map (homOfLE (Nat.le_succ n)).op :=
    (extend n (lifts n)).choose_spec.symm
  let b : P ⟶ J :=
    { f := fun i ↦ NatTrans.ofOpSequence (fun n ↦ (lifts n).val.f i)
        (fun n ↦ congrArg (fun a ↦ HomologicalComplex.Hom.f a i) (compat n))
      comm' := by
        intro i j hij
        ext n
        exact (lifts n.unop).val.comm i j }
  exact ⟨b, fun n ↦ (lifts n).property⟩

variable {C : Type u} [SmallCategory C] {τ : GrothendieckTopology C}
  (R : Sheaf τ RingCat.{u})
  [HasDerivedCategory.{wA} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]

end CategoryTheory
