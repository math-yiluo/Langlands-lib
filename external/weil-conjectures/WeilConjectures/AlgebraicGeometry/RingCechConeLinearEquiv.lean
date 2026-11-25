/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.Order.Fin.Tuple
public import Mathlib.RingTheory.Localization.BaseChange

/-! # The linear equivalence underlying the localization cone

Source: Stacks Project, more-algebra.tex, section-alternating-cech, and
algebra.tex, localization base change.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open scoped BigOperators TensorProduct
namespace CategoryTheory

/-- The augmented ordered localization terms.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
abbrev ringCechTailTerm (A : CommRingCat.{u}) (r : ℕ) (g : Fin r → A) :
    ℕ → ModuleCat.{u} A
  | 0 => ModuleCat.of A A
  | q + 1 => ModuleCat.of A
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, g (t i)))

/-- Shift an ordered subset past zero.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechShift {q r : ℕ} (t : Fin q ↪o Fin r) : Fin q ↪o Fin (r + 1) :=
  t.trans (Fin.succOrderEmb r)

/-- Adjoin zero to an ordered subset.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechCons {q r : ℕ} (t : Fin q ↪o Fin r) :
    Fin (q + 1) ↪o Fin (r + 1) :=
  OrderEmbedding.ofStrictMono (Fin.cons 0 (fun i ↦ (t i).succ))
    (Fin.strictMono_cons.mpr ⟨fun _ ↦ Fin.succ_pos _, Fin.strictMono_succ.comp t.strictMono⟩)

/-- Remove zero from the domain and subtract one from the remaining values.
Source: the ordered-subset partition in Stacks Project, more-algebra.tex,
section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechTailPred {q r : ℕ} (t : Fin (q + 1) ↪o Fin (r + 1)) :
    Fin q ↪o Fin r :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (t i.succ).pred (ne_of_gt (lt_of_le_of_lt (Fin.zero_le (t 0))
      (t.strictMono (Fin.succ_pos i)))))
    (Fin.strictMono_pred_comp _ (t.strictMono.comp Fin.strictMono_succ))

/-- Subtract one from every value of a subset avoiding zero.
Source: the ordered-subset partition in Stacks Project, more-algebra.tex,
section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechAllPred {q r : ℕ} (t : Fin (q + 1) ↪o Fin (r + 1)) (h : t 0 ≠ 0) :
    Fin (q + 1) ↪o Fin r :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (t i).pred (ne_of_gt (lt_of_lt_of_le (Fin.pos_iff_ne_zero.mpr h)
      (t.monotone (Fin.zero_le i)))))
    (Fin.strictMono_pred_comp _ t.strictMono)

/-- Recover a subset containing zero from its tail.
Source: the ordered-subset partition in Stacks Project, more-algebra.tex,
section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem cons_ringCechTailPred {q r : ℕ} (t : Fin (q + 1) ↪o Fin (r + 1))
    (h : t 0 = 0) : ringCechCons (ringCechTailPred t) = t := by
  ext i
  cases i using Fin.cases <;> simp [ringCechCons, ringCechTailPred, h]

/-- Recover a subset avoiding zero from its predecessor.
Source: the ordered-subset partition in Stacks Project, more-algebra.tex,
section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem shift_ringCechAllPred {q r : ℕ} (t : Fin (q + 1) ↪o Fin (r + 1))
    (h : t 0 ≠ 0) : ringCechShift (ringCechAllPred t h) = t := by
  ext i
  simp [ringCechShift, ringCechAllPred]

/-- Ordered nonempty subsets split according to whether they contain zero.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechIndexEquiv (q r : ℕ) :
    ((Fin (q + 1) ↪o Fin r) ⊕ (Fin q ↪o Fin r)) ≃
      (Fin (q + 1) ↪o Fin (r + 1)) :=
  Equiv.ofBijective (Sum.elim ringCechShift ringCechCons) (by
    constructor
    · intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          congr 1
          ext i
          exact congrArg Fin.val (Fin.succ_injective _ (congrArg (fun t ↦ t i) h))
        | inr b =>
          have hh := congrArg (fun t ↦ (t 0).val) h
          simp [ringCechShift, ringCechCons] at hh
      | inr a =>
        cases b with
        | inl b =>
          have hh := congrArg (fun t ↦ (t 0).val) h
          simp [ringCechShift, ringCechCons] at hh
        | inr b =>
          congr 1
          ext i
          exact congrArg Fin.val (Fin.succ_injective _ (congrArg (fun t ↦ t i.succ) h))
    · intro t
      by_cases h : t 0 = 0
      · exact ⟨Sum.inr (ringCechTailPred t), cons_ringCechTailPred t h⟩
      · exact ⟨Sum.inl (ringCechAllPred t h), shift_ringCechAllPred t h⟩)

/-- The canonical map between away localizations when one denominator divides another.
Source: Stacks Project, more-algebra.tex, section-alternating-cech, canonical face maps.
(auxiliary; not a blueprint node). -/
def ringCechLocMap (A : CommRingCat.{u}) (a b : A) (h : a ∣ b) :
    Localization.Away a →ₐ[A] Localization.Away b :=
  IsLocalization.Away.liftAlgHom a (f := Algebra.ofId A _)
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away b) b h)

/-- Uniqueness of maps out of an away localization.
Source: Stacks Project, algebra.tex, localization universal property.
(auxiliary; not a blueprint node). -/
theorem ringCechLocMap_unique (A : CommRingCat.{u}) (a : A)
    {B : Type u} [CommRing B] [Algebra A B]
    (h k : Localization.Away a →ₐ[A] B) : h = k := by
  apply IsLocalization.algHom_ext (Submonoid.powers a)
  exact Subsingleton.elim _ _

/-- The localization map attached to deleting a vertex.
Source: Stacks Project, more-algebra.tex, section-alternating-cech, formula (2).
(auxiliary; not a blueprint node). -/
def ringCechFace (A : CommRingCat.{u}) {r : ℕ} (f : Fin r → A)
    (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)) :
    Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
      Localization.Away (∏ i, f (t i)) :=
  ringCechLocMap A _ _ (by
    rw [Fin.prod_univ_succAbove _ j]
    exact dvd_mul_left _ _)

/-- Localizing two elements successively gives localization at their product.
Source: Stacks Project, algebra.tex, localization base change.
(auxiliary; not a blueprint node). -/
def ringCechTensorAway (A : CommRingCat.{u}) (a b : A) :
    (Localization.Away a ⊗[A] Localization.Away b) ≃ₐ[A]
      Localization.Away (a * b) := by
  let S := Localization.Away a
  let T := S ⊗[A] Localization.Away b
  letI : IsLocalization.Away (a * b) T :=
    IsLocalization.Away.mul' S T a b
  exact IsLocalization.algEquiv (Submonoid.powers (a * b)) T _

/-- The coefficient of a subset containing zero.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechHeadCoeff (A : CommRingCat.{u}) {r q : ℕ} (f : Fin (r + 1) → A)
    (t : Fin q ↪o Fin r) :
    Localization.Away (f 0 * ∏ i, f (t i).succ) ≃ₐ[A]
      Localization.Away (∏ i, f (ringCechCons t i)) := by
  have h : (∏ i, f (ringCechCons t i)) = f 0 * ∏ i, f (t i).succ := by
    simp [Fin.prod_univ_succ, ringCechCons]
  rw [h]

/-- Tensor coefficients at the subsets containing zero, including the augmented term.
Source: Stacks Project, algebra.tex, localization base change, and
more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechHeadEquiv (A : CommRingCat.{u}) (r q : ℕ) (f : Fin (r + 1) → A) :
    (Localization.Away (f 0) ⊗[A] ringCechTailTerm A r (fun i ↦ f i.succ) q) ≃ₗ[A]
      ((t : Fin q ↪o Fin r) → Localization.Away (∏ i, f (ringCechCons t i))) := by
  classical
  cases q with
  | zero =>
    have h (t : Fin 0 ↪o Fin r) : (∏ i, f (ringCechCons t i)) = f 0 := by
      simp [ringCechCons]
    letI : Unique (Fin 0 ↪o Fin r) :=
      ⟨⟨OrderEmbedding.ofStrictMono Fin.elim0 (by intro i; exact Fin.elim0 i)⟩,
        fun t ↦ by ext i; exact Fin.elim0 i⟩
    let e (t : Fin 0 ↪o Fin r) : Localization.Away (f 0) ≃ₐ[A]
        Localization.Away (∏ i, f (ringCechCons t i)) := by
      rw [h]
    exact (TensorProduct.rid A _).trans
      ((LinearEquiv.piUnique _ _).symm.trans (LinearEquiv.piCongrRight
        (fun t ↦ (e t).toLinearEquiv)))
  | succ q =>
    exact (TensorProduct.piRight A A (Localization.Away (f 0)) _).trans
      (LinearEquiv.piCongrRight (fun t ↦
        ((ringCechTensorAway A (f 0) (∏ i, f (t i).succ)).trans
          (ringCechHeadCoeff A f t)).toLinearEquiv))

/-- Assemble two dependent products over a disjoint union.
Source: the ordered-subset partition in Stacks Project, more-algebra.tex,
section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechSumPiEquiv (A : Type u) [CommRing A] {I J : Type*}
    (V : I ⊕ J → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] :
    ((∀ i, V (Sum.inl i)) × (∀ j, V (Sum.inr j))) ≃ₗ[A] (∀ k, V k) where
  toFun x := Sum.rec x.1 x.2
  invFun x := (fun i ↦ x (.inl i), fun j ↦ x (.inr j))
  left_inv _ := rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' a x := by funext i; cases i <;> rfl

/-- The explicit degreewise linear equivalence from the two blocks to full coordinates.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechConeEquiv (A : CommRingCat.{u}) (r q : ℕ) (f : Fin (r + 1) → A) :
    (ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1) ×
      (Localization.Away (f 0) ⊗[A] ringCechTailTerm A r (fun i ↦ f i.succ) q)) ≃ₗ[A]
      ((t : Fin (q + 1) ↪o Fin (r + 1)) → Localization.Away (∏ i, f (t i))) :=
  by
  let V := fun (t : Fin (q + 1) ↪o Fin (r + 1)) ↦ Localization.Away (∏ i, f (t i))
  let e := ringCechIndexEquiv q r
  let s : ((∀ t : Fin (q + 1) ↪o Fin r, V (e (.inl t))) ×
      (∀ t : Fin q ↪o Fin r, V (e (.inr t)))) ≃ₗ[A] (∀ k, V (e k)) :=
    ringCechSumPiEquiv A (fun k ↦ V (e k))
  let p : (∀ k, V (e k)) ≃ₗ[A] (∀ t, V t) := LinearEquiv.piCongrLeft A V e
  exact ((LinearEquiv.refl A _).prodCongr (ringCechHeadEquiv A r q f)).trans (s.trans p)

/-- Evaluation after reindexing a dependent product.
Source: the definition of dependent reindexing.
(auxiliary; not a blueprint node). -/
theorem ringCechPiCongr_apply {R : Type*} [CommRing R] {I J : Type*}
    (V : J → Type*) [∀ j, AddCommGroup (V j)] [∀ j, Module R (V j)]
    (e : I ≃ J) (x : ∀ i, V (e i)) (i : I) :
    LinearEquiv.piCongrLeft R V e x (e i) = x i := by
  exact congrFun ((LinearEquiv.piCongrLeft' R V e.symm).apply_symm_apply x) i

/-- The first block evaluates at subsets avoiding zero.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem ringCechConeEquiv_shift (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A)
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (y : Localization.Away (f 0) ⊗[A] ringCechTailTerm A r (fun i ↦ f i.succ) q)
    (t : Fin (q + 1) ↪o Fin r) :
    ringCechConeEquiv A r q f (x, y) (ringCechShift t) = x t := by
  change LinearEquiv.piCongrLeft A (fun t ↦ Localization.Away (∏ i, f (t i)))
    (ringCechIndexEquiv q r) _
    (ringCechIndexEquiv q r (Sum.inl t)) = _
  rw [ringCechPiCongr_apply]
  rfl

/-- The second block evaluates at subsets containing zero.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem ringCechConeEquiv_cons (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A)
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (y : Localization.Away (f 0) ⊗[A] ringCechTailTerm A r (fun i ↦ f i.succ) q)
    (t : Fin q ↪o Fin r) :
    ringCechConeEquiv A r q f (x, y) (ringCechCons t) = ringCechHeadEquiv A r q f y t := by
  change LinearEquiv.piCongrLeft A (fun t ↦ Localization.Away (∏ i, f (t i)))
    (ringCechIndexEquiv q r) _
    (ringCechIndexEquiv q r (Sum.inr t)) = _
  rw [ringCechPiCongr_apply]
  rfl

/-- The map of the first localization into a coordinate containing zero.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechHeadLeft (A : CommRingCat.{u}) {r q : ℕ} (f : Fin (r + 1) → A)
    (t : Fin q ↪o Fin r) :
    Localization.Away (f 0) →ₐ[A] Localization.Away (∏ i, f (ringCechCons t i)) :=
  (ringCechHeadCoeff A f t).toAlgHom.comp
    (ringCechLocMap A _ _ (dvd_mul_right (f 0) (∏ i, f (t i).succ)))

/-- The map of the tail localization into a coordinate containing zero.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
def ringCechHeadRight (A : CommRingCat.{u}) {r q : ℕ} (f : Fin (r + 1) → A)
    (t : Fin q ↪o Fin r) :
    Localization.Away (∏ i, f (t i).succ) →ₐ[A]
      Localization.Away (∏ i, f (ringCechCons t i)) :=
  (ringCechHeadCoeff A f t).toAlgHom.comp
    (ringCechLocMap A _ _ (dvd_mul_left (∏ i, f (t i).succ) (f 0)))

/-- The degree-zero second block is scalar multiplication followed by localization.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem ringCechHeadEquiv_zero_tmul (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin (r + 1) → A) (s : Localization.Away (f 0)) (x : A)
    (t : Fin 0 ↪o Fin r) :
    ringCechHeadEquiv A r 0 f (s ⊗ₜ[A] x) t =
      ringCechHeadLeft A f t s * algebraMap A _ x := by
  simp only [ringCechHeadEquiv]
  let e : Localization.Away (f 0) ≃ₐ[A]
      Localization.Away (∏ i, f (ringCechCons t i)) := by
    have h : (∏ i, f (ringCechCons t i)) = f 0 := by simp [ringCechCons]
    rw [h]
  change e (x • s) = _
  rw [map_smul, Algebra.smul_def, mul_comm]
  congr 1
  exact congrArg (fun h : Localization.Away (f 0) →ₐ[A] _ ↦ h s)
    (ringCechLocMap_unique A _ e.toAlgHom (ringCechHeadLeft A f t))

/-- On pure tensors, the second block multiplies the two canonical localization maps.
Source: Stacks Project, algebra.tex, localization base change.
(auxiliary; not a blueprint node). -/
theorem ringCechHeadEquiv_succ_tmul (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A) (s : Localization.Away (f 0))
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (t : Fin (q + 1) ↪o Fin r) :
    ringCechHeadEquiv A r (q + 1) f (s ⊗ₜ[A] x) t =
      ringCechHeadLeft A f t s * ringCechHeadRight A f t (x t) := by
  let S := Localization.Away (f 0)
  let b := ∏ i, f (t i).succ
  let T := S ⊗[A] Localization.Away b
  let : IsLocalization.Away (f 0 * b) T :=
    IsLocalization.Away.mul' S T (f 0) b
  let h : T →ₐ[A] Localization.Away (∏ i, f (ringCechCons t i)) :=
    (ringCechHeadCoeff A f t).toAlgHom.comp (ringCechTensorAway A (f 0) b).toAlgHom
  let k : T →ₐ[A] Localization.Away (∏ i, f (ringCechCons t i)) :=
    Algebra.TensorProduct.lift (ringCechHeadLeft A f t) (ringCechHeadRight A f t)
      (fun _ _ ↦ Commute.all _ _)
  have hk : h = k := by
    apply IsLocalization.algHom_ext (Submonoid.powers (f 0 * b))
    exact Subsingleton.elim _ _
  change h (s ⊗ₜ[A] (x t)) = k (s ⊗ₜ[A] (x t))
  rw [hk]

/-- Deleting a nonzero vertex of an adjoined-zero subset preserves its leading zero.
Source: Stacks Project, more-algebra.tex, section-alternating-cech.
(auxiliary; not a blueprint node). -/
theorem ringCechCons_face_succ {q r : ℕ} (t : Fin (q + 1) ↪o Fin r)
    (j : Fin (q + 1)) :
    (Fin.succAboveOrderEmb j.succ).trans (ringCechCons t) =
      ringCechCons ((Fin.succAboveOrderEmb j).trans t) := by
  ext i
  cases i using Fin.cases with
  | zero => simp [ringCechCons, Fin.succAboveOrderEmb]
  | succ i =>
    cases q with
    | zero => exact Fin.elim0 i
    | succ q => simp [ringCechCons, Fin.succAboveOrderEmb]

end CategoryTheory
