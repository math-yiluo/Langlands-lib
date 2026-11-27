import Langlands.BaseChange.TwistedLocalDescent.Duality
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Ring.GeomSum

/-! # The entrywise sup norm on matrices over an ultrametric field

Over a normed field with ultrametric absolute value, the entrywise sup norm on square matrices
is submultiplicative; strictly block lower matrices are nilpotent, so `1 + Z` has the finite
geometric series as inverse, of norm at most one when `‖Z‖ ≤ 1`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear Finset

universe v

attribute [local instance] Matrix.normedAddCommGroup

section Norm

variable {𝕂 : Type v} [NormedField 𝕂] [IsUltrametricDist 𝕂] {n : ℕ}

omit [IsUltrametricDist 𝕂] in
/-- The sup norm on matrices over an ultrametric field is ultrametric. -/
theorem matrix_isUltrametricDist [IsUltrametricDist 𝕂] :
    IsUltrametricDist (Matrix (Fin n) (Fin n) 𝕂) :=
  (inferInstance : IsUltrametricDist (Fin n → Fin n → 𝕂))

attribute [local instance] matrix_isUltrametricDist

/-- The entrywise sup norm is submultiplicative over an ultrametric field. -/
theorem matrix_norm_mul_le (X Y : Matrix (Fin n) (Fin n) 𝕂) : ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
  rw [Matrix.norm_le_iff (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  intro i k
  rw [Matrix.mul_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro j _
  rw [norm_mul]
  exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm X)
    (Matrix.norm_entry_le_entrywise_sup_norm Y) (norm_nonneg _) (norm_nonneg _)

omit [IsUltrametricDist 𝕂] in
theorem matrix_norm_one_le : ‖(1 : Matrix (Fin n) (Fin n) 𝕂)‖ ≤ 1 := by
  rw [Matrix.norm_le_iff zero_le_one]
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem matrix_norm_pow_le (X : Matrix (Fin n) (Fin n) 𝕂) (t : ℕ) : ‖X ^ t‖ ≤ ‖X‖ ^ t := by
  induction t with
  | zero => simpa using matrix_norm_one_le
  | succ t ih =>
    rw [pow_succ, pow_succ]
    exact (matrix_norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

omit [IsUltrametricDist 𝕂] in
theorem matrix_norm_map_eq (X : Matrix (Fin n) (Fin n) 𝕂) (σ : 𝕂 → 𝕂) (hσ : ∀ a, ‖σ a‖ = ‖a‖) :
    ‖X.map σ‖ = ‖X‖ :=
  Matrix.norm_map_eq X σ hσ

end Norm

section Nilpotent

variable {R : Type v} [CommRing R] {n : ℕ} (B : BlockShape n)

/-- Matrices whose nonzero entries go down at least `t` blocks. -/
def lowerLevel (t : ℕ) : Set (Matrix (Fin n) (Fin n) R) :=
  {Y | ∀ a b, Y a b ≠ 0 → (B.coordinateBlock b).val + t ≤ (B.coordinateBlock a).val}

theorem mul_mem_lowerLevel {s t : ℕ} {Y Z : Matrix (Fin n) (Fin n) R} (hY : Y ∈ lowerLevel B s)
    (hZ : Z ∈ lowerLevel B t) : Y * Z ∈ lowerLevel B (s + t) := by
  intro a b hab
  rw [Matrix.mul_apply] at hab
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  have h1 := hY a c (left_ne_zero_of_mul hc)
  have h2 := hZ c b (right_ne_zero_of_mul hc)
  omega

theorem pow_mem_lowerLevel {Z : Matrix (Fin n) (Fin n) R} (hZ : Z ∈ lowerLevel B 1) (t : ℕ) :
    Z ^ (t + 1) ∈ lowerLevel B (t + 1) := by
  induction t with
  | zero => simpa using hZ
  | succ t ih =>
    rw [pow_succ]
    exact mul_mem_lowerLevel B ih hZ

theorem eq_zero_of_mem_lowerLevel {Y : Matrix (Fin n) (Fin n) R} (hY : Y ∈ lowerLevel B B.length) :
    Y = 0 := by
  ext a b
  by_contra h
  have := hY a b h
  have := (B.coordinateBlock a).isLt
  omega

theorem mem_lowerLevel_one_of_mem_lowerLie {Z : Matrix (Fin n) (Fin n) R}
    (hZ : ∀ a b, B.coordinateBlock a ≤ B.coordinateBlock b → Z a b = 0) :
    Z ∈ lowerLevel B 1 := by
  intro a b hab
  by_contra h
  exact hab (hZ a b (by
    rw [Fin.le_def]
    omega))

/-- Strictly block lower matrices are nilpotent. -/
theorem pow_length_eq_zero {Z : Matrix (Fin n) (Fin n) R}
    (hZ : ∀ a b, B.coordinateBlock a ≤ B.coordinateBlock b → Z a b = 0) :
    Z ^ B.length = 0 := by
  rcases Nat.eq_zero_or_pos B.length with h | h
  · ext a
    exact absurd (B.coordinateBlock a).isLt (by omega)
  · obtain ⟨t, ht⟩ : ∃ t, B.length = t + 1 := ⟨B.length - 1, by omega⟩
    have := pow_mem_lowerLevel B (mem_lowerLevel_one_of_mem_lowerLie B hZ) t
    rw [← ht] at this
    exact eq_zero_of_mem_lowerLevel B this

/-- The inverse of `1 + Z` for strictly block lower `Z`, as a finite geometric series. -/
def lowerInverse (Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  ∑ t ∈ range B.length, (-Z) ^ t

theorem one_add_mul_lowerInverse {Z : Matrix (Fin n) (Fin n) R}
    (hZ : ∀ a b, B.coordinateBlock a ≤ B.coordinateBlock b → Z a b = 0) :
    (1 + Z) * lowerInverse B Z = 1 := by
  have h := mul_neg_geom_sum (-Z) B.length
  rw [sub_neg_eq_add, neg_pow, pow_length_eq_zero B hZ, mul_zero, sub_zero] at h
  exact h

theorem lowerInverse_mul_one_add {Z : Matrix (Fin n) (Fin n) R}
    (hZ : ∀ a b, B.coordinateBlock a ≤ B.coordinateBlock b → Z a b = 0) :
    lowerInverse B Z * (1 + Z) = 1 := by
  have h := geom_sum_mul_neg (-Z) B.length
  rw [sub_neg_eq_add, neg_pow, pow_length_eq_zero B hZ, mul_zero, sub_zero] at h
  exact h

end Nilpotent

section InverseNorm

attribute [local instance] matrix_isUltrametricDist

variable {𝕂 : Type v} [NormedField 𝕂] [IsUltrametricDist 𝕂] {n : ℕ} (B : BlockShape n)

theorem norm_lowerInverse_le {Z : Matrix (Fin n) (Fin n) 𝕂} (hZ1 : ‖Z‖ ≤ 1) :
    ‖lowerInverse B Z‖ ≤ 1 := by
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro t _
  refine (matrix_norm_pow_le _ t).trans ?_
  rw [norm_neg]
  exact pow_le_one₀ (norm_nonneg _) hZ1

end InverseNorm

end Langlands.BaseChange.TwistedLocalDescent
