/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# The Koszul differential on the exterior algebra

Let `R` be a commutative ring, `M` an `R`-module and `φ : Module.Dual R M`. The Koszul
differential `ExteriorAlgebra.koszulDifferential φ` is the left contraction
`CliffordAlgebra.contractLeft φ` on `ExteriorAlgebra R M = CliffordAlgebra 0`. It is the unique
`R`-linear map `D` with `D 1 = 0` and `D (v ∧ x) = φ v • x - v ∧ D x`; it lowers degrees by one,
is given on `v₁ ∧ ⋯ ∧ vₙ` by the usual alternating-sum formula, and is a graded derivation of
degree `-1` (Stacks, Tag 0622).

## Main results

* `ExteriorAlgebra.eq_koszulDifferential`, `ExteriorAlgebra.koszulDifferential_mem_exteriorPower`,
  `ExteriorAlgebra.koszulDifferential_ιMulti`, `ExteriorAlgebra.koszulDifferential_mul`,
  `ExteriorAlgebra.eq_koszulDifferential_of_derivation`.

The packaged existence-and-uniqueness statement is `ExteriorAlgebra.koszul_differential` in
`WeilConjectures.AlgebraicGeometry.KoszulDifferential`.
-/

@[expose] public section

namespace ExteriorAlgebra

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The Koszul differential `D_φ` on `⋀ M` associated with `φ : M →ₗ[R] R`, realised as the
left contraction by `φ`. -/
def koszulDifferential (φ : Dual R M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft (Q := 0) φ

variable (φ : Dual R M)

@[simp]
theorem koszulDifferential_one : koszulDifferential φ 1 = 0 :=
  CliffordAlgebra.contractLeft_one (Q := 0) φ

theorem koszulDifferential_ι_mul (v : M) (x : ExteriorAlgebra R M) :
    koszulDifferential φ (ι R v * x) = φ v • x - ι R v * koszulDifferential φ x :=
  CliffordAlgebra.contractLeft_ι_mul (Q := 0) φ v x

@[simp]
theorem koszulDifferential_ι (v : M) :
    koszulDifferential φ (ι R v) = algebraMap R (ExteriorAlgebra R M) (φ v) :=
  CliffordAlgebra.contractLeft_ι (Q := 0) φ v

@[simp]
theorem koszulDifferential_algebraMap (r : R) :
    koszulDifferential φ (algebraMap R (ExteriorAlgebra R M) r) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap (Q := 0) φ r

/-- Uniqueness of a linear map `D` with `D 1 = 0` and `D (v ∧ x) = φ v • x - v ∧ D x`. -/
theorem eq_koszulDifferential {D : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M}
    (h1 : D 1 = 0) (hmul : ∀ v x, D (ι R v * x) = φ v • x - ι R v * D x) :
    D = koszulDifferential φ := by
  ext x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h1, koszulDifferential_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul x v hx =>
    rw [show CliffordAlgebra.ι (0 : QuadraticForm R M) v = ι R v from rfl, hmul,
      koszulDifferential_ι_mul, hx]

/-- `D_φ` maps `⋀ⁿ M` to `⋀ⁿ⁻¹ M`, and kills `⋀⁰ M`. -/
theorem koszulDifferential_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) :
    (n = 0 → koszulDifferential φ x = 0) ∧ koszulDifferential φ x ∈ ⋀[R]^(n - 1) M := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i _ _ ihx ihy =>
    exact ⟨fun h ↦ by rw [map_add, ihx.1 h, ihy.1 h, add_zero], by
      rw [map_add]; exact add_mem ihx.2 ihy.2⟩
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    refine ⟨fun h ↦ absurd h (Nat.succ_ne_zero _), ?_⟩
    rw [koszulDifferential_ι_mul]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    rcases i with _ | i
    · rw [ih.1 rfl, mul_zero]; exact zero_mem _
    · have := Submodule.mul_mem_mul (LinearMap.mem_range_self (ι R) v) ih.2
      rwa [← pow_succ'] at this

/-- The explicit formula `D(v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1)ⁱ φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem koszulDifferential_ιMulti (n : ℕ) (v : Fin (n + 1) → M) :
    koszulDifferential φ (ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • φ (v i) • ιMulti R n (i.removeNth v) := by
  induction n with
  | zero => simp [ιMulti_succ_apply, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    rw [ιMulti_succ_apply, koszulDifferential_ι_mul, ih, Finset.mul_sum, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    conv_rhs => rw [Fin.sum_univ_succ]
    congr 1
    · rw [Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero]; rfl
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      have h0 : Fin.removeNth j.succ v 0 = v 0 := by
        simp [Fin.removeNth_apply]
      have ht : Matrix.vecTail (Fin.removeNth j.succ v) = Fin.removeNth j (Matrix.vecTail v) := by
        funext k
        simp [Matrix.vecTail, Fin.removeNth_apply, Fin.succ_succAbove_succ]
      rw [ιMulti_succ_apply, h0, ht, mul_smul_comm, mul_smul_comm, Fin.val_succ, pow_succ,
        mul_neg_one, neg_smul]
      rfl

/-- `D_φ` is a graded derivation of degree `-1`. -/
theorem koszulDifferential_mul {m : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^m M)
    (y : ExteriorAlgebra R M) :
    koszulDifferential φ (x * y) =
      koszulDifferential φ x * y + (-1 : R) ^ m • (x * koszulDifferential φ y) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simp [Algebra.algebraMap_eq_smul_one]
  | add x x' i _ _ ihx ihx' =>
    rw [add_mul, map_add, ihx, ihx', map_add, add_mul, add_mul, smul_add]
    abel
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [mul_assoc, koszulDifferential_ι_mul, ih, koszulDifferential_ι_mul, sub_mul, mul_add,
      smul_mul_assoc, mul_smul_comm, pow_succ, mul_neg_one, neg_smul, mul_assoc, mul_assoc]
    abel

/-- Uniqueness of the Koszul differential as a graded derivation of degree `-1` extending `φ`. -/
theorem eq_koszulDifferential_of_derivation {D : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M}
    (hmul : ∀ (m : ℕ) (x : ExteriorAlgebra R M), x ∈ ⋀[R]^m M → ∀ y,
      D (x * y) = D x * y + (-1 : R) ^ m • (x * D y))
    (hι : ∀ v, D (ι R v) = algebraMap R _ (φ v)) :
    D = koszulDifferential φ := by
  have h1 : D 1 = 0 := by
    have := hmul 0 1 (by simp) 1
    simp only [mul_one, pow_zero, one_smul, one_mul] at this
    simpa using this
  refine eq_koszulDifferential φ h1 fun v x ↦ ?_
  have hv : ι R v ∈ ⋀[R]^1 M := by simp
  rw [hmul 1 _ hv, hι, pow_one, neg_one_smul, Algebra.smul_def, sub_eq_add_neg]

end ExteriorAlgebra
