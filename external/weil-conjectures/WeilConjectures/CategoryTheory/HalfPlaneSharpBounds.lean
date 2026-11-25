/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import Mathlib.Data.Int.Interval

/-! Canonical truncation-couple proof step. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem pullback_bot_eq_kernel
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {V W : B} (f : V ⟶ W) :
    (Subobject.pullback f).obj ⊥ = kernelSubobject f := by
  apply le_antisymm
  · apply le_kernelSubobject
    apply (Subobject.bot_factors_iff_zero _).mp
    apply (pullback_factors_iff f _ _).mp
    exact Subobject.factors_self _
  · apply Subobject.le_of_factors
    apply (pullback_factors_iff f _ _).mpr
    exact (Subobject.bot_factors_iff_zero _).mpr (kernelSubobject_arrow_comp f)

/-- Sharp numerical stabilization bounds for a lower-half-plane exact couple.
Source: Stacks Tags 011T, 0BDU, 0BDV; blueprint steps 3--5 of
lemma-uniform-bound-proper-direct-image--1 (blueprint: lem-sp-half-plane-sharp-bounds).

Proof: Each later E term is a subquotient of the initial E term, so induction
preserves its lower-half-plane support. A nonzero term therefore has p>=0 and
q>=a; on a total-degree diagonal this leaves finitely many indices, proving
boundedness. The outgoing differential has zero target when r>q-a+1, and the
incoming differential has zero source when r>p. The defining recurrences for
cycles and boundaries then become equalities from max(2,q-a+2,p+1) onwards;
induction gives the displayed equalities with their initial stable values.
This proves regularity. The source of the incoming alpha iterate is D(p+r,q-r),
zero when r>q-a, so its image is bottom. For each bidegree these images are
therefore eventually bottom, proving completeness. -/
theorem halfPlane_sharp_bounds
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q)) :
      (∀ (r : ℕ) (p q : ℤ), 2 ≤ r → (p < 0 ∨ q < a) → IsZero (X.page r p q)) ∧
      (∀ (r : ℕ) (p q : ℤ), 2 ≤ r → ¬ IsZero (X.page r p q) →
        a ≤ q ∧ q ≤ p + q ∧ 0 ≤ p ∧ p ≤ p + q - a) ∧
      X.IsBounded ∧
      (∀ (r : ℕ) (p q : ℤ), 2 ≤ r → max (q - a + 1) p < (r : ℤ) →
        (X.pageCouple (r - 2)).d p q = 0 ∧
          (X.pageCouple (r - 2)).dInto p q = 0) ∧
      (∀ (p q : ℤ) (t : ℕ), max 2 (max (q - a + 2) (p + 1)) ≤ (t : ℤ) →
        X.cycleBoundaryTower.Z (t - 2) p q =
          X.cycleBoundaryTower.Z ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
        X.cycleBoundaryTower.B (t - 2) p q =
          X.cycleBoundaryTower.B ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q) ∧
      X.IsRegular ∧
      (∀ (r : ℕ) (p q : ℤ), q - a < (r : ℤ) →
        imageSubobject (X.incomingAlphaIter r p q) = ⊥) ∧
      X.IsComplete := by
  classical
  have hzero : ∀ (r : ℕ) (p q : ℤ),
      (p < 0 ∨ q < a) → IsZero ((X.pageCouple r).E p q) := by
    intro r
    induction r with
    | zero => exact hE
    | succ r ih =>
      intro p q h
      change IsZero (cokernel _)
      apply IsZero.of_epi (cokernel.π _)
      exact IsZero.of_mono (kernel.ι ((X.pageCouple r).d p q)) (ih p q h)
  have hpage : ∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (p < 0 ∨ q < a) → IsZero (X.page r p q) := by
    intro r p q _ h
    exact hzero (r - 2) p q h
  have hd : ∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      max (q - a + 1) p < (r : ℤ) →
      (X.pageCouple (r - 2)).d p q = 0 ∧
        (X.pageCouple (r - 2)).dInto p q = 0 := by
    intro r p q hr h
    constructor
    · apply IsZero.eq_zero_of_tgt
      exact hzero (r - 2) _ _ (Or.inr (by omega))
    · apply IsZero.eq_zero_of_src
      exact hzero (r - 2) _ _ (Or.inl (by omega))
  have himage : ∀ (r : ℕ) (p q : ℤ), q - a < (r : ℤ) →
      imageSubobject (X.incomingAlphaIter r p q) = ⊥ := by
    intro r p q h
    rw [(hD (p + r) (q - r) (by omega)).eq_zero_of_src
      (X.incomingAlphaIter r p q),
      imageSubobject_zero]
  obtain ⟨L, A, hA, hι, hsupport, hstab, hfull, hfinite, hgr, hcomplete, hconv⟩ :=
    X.halfPlaneConvergence a hD hE
  refine ⟨hpage, ?_, ?_, hd, ?_, hconv.1, himage, hcomplete⟩
  · intro r p q hr h
    have hn := hsupport (r - 2) (p + q) p q rfl h
    omega
  · intro n
    apply (Set.finite_Icc a n).image (fun q : ℤ ↦ (n - q, q)) |>.subset
    intro pq hpq
    have htotal := hpq.1
    have hp := hsupport 0 n pq.1 pq.2 hpq.1 hpq.2
    refine ⟨pq.2, hp, ?_⟩
    apply Prod.ext
    · dsimp
      omega
    · rfl
  · intro p q t ht
    let k : ℤ := max 2 (max (q - a + 2) (p + 1))
    have hk : 2 ≤ k := le_max_left _ _
    have hs : ∀ m : ℕ, k.toNat - 2 ≤ m →
        X.cycleBoundaryTower.Z (m + 1) p q = X.cycleBoundaryTower.Z m p q ∧
        X.cycleBoundaryTower.B (m + 1) p q = X.cycleBoundaryTower.B m p q := by
      intro m hm
      have hb : max (q - a + 1) p < ((m + 2 : ℕ) : ℤ) := by
        dsimp [k] at *
        omega
      obtain ⟨ho, hi⟩ := hd (m + 2) p q (by omega) hb
      have heq : m + 2 - 2 = m := by omega
      rw [heq] at ho hi
      constructor
      · rw [X.cycleBoundaryTower.Z_succ, ho, kernelSubobject_zero,
          Subobject.pullback_top, Subobject.exists_iso_map, Subobject.map_top,
          Subobject.mk_arrow]
      · rw [X.cycleBoundaryTower.B_succ, hi, imageSubobject_zero,
          pullback_bot_eq_kernel, X.cycleBoundaryTower.projection_kernel,
          Subobject.exists_iso_map, Subobject.map_mk]
        simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]
    have hconst : ∀ m : ℕ, k.toNat - 2 ≤ m →
        X.cycleBoundaryTower.Z m p q = X.cycleBoundaryTower.Z (k.toNat - 2) p q ∧
        X.cycleBoundaryTower.B m p q = X.cycleBoundaryTower.B (k.toNat - 2) p q := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact ⟨rfl, rfl⟩
      | succ m hm ih =>
        exact ⟨(hs m hm).1.trans ih.1, (hs m hm).2.trans ih.2⟩
    exact hconst (t - 2) (by dsimp [k] at *; omega)

end CategoryTheory
