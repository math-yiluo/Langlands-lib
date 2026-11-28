import Langlands.LinearAlgebra.ClassicalCartanDeterminants
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! # Integral index of two A2 pairs in type D4 -/

open Matrix

namespace Langlands.LinearAlgebra

/-- The Gram matrix for two root pairs `[α, σα]` and `[β, σβ]`, with each
pair of type A2 and the cyclic action preserving the pairing. -/
private def cyclicPairGram (a b c : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, a, b; -1, 2, c, a; a, c, 2, -1; b, a, -1, 2]

private theorem det_cyclicPairGram (a b c : ℤ)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) (hc : -1 ≤ c ∧ c ≤ 1)
    (hsum : a + b + c = 0) (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (cyclicPairGram a b c).det = 4 := by
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  obtain ⟨hc₁, hc₂⟩ := hc
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | decide

/-- In the D4 coroot lattice, two A2 pairs with this cyclic Gram pattern
and a nonzero cross pairing have index one. The columns of `M` are the
four coroots in a numbered simple-coroot basis. -/
theorem isUnit_det_of_D4_cyclicPairGram (M : Matrix (Fin 4) (Fin 4) ℤ) (a b c : ℤ)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) (hc : -1 ≤ c ∧ c ≤ 1)
    (hsum : a + b + c = 0) (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (hM : Mᵀ * CartanMatrix.D 4 * M =
      !![2, -1, a, b; -1, 2, c, a; a, c, 2, -1; b, a, -1, 2]) : IsUnit M.det := by
  have h : (Mᵀ * CartanMatrix.D 4 * M).det = 4 := by
    rw [hM]
    exact det_cyclicPairGram a b c ha hb hc hsum hnonzero
  rw [det_mul, det_mul, det_transpose, cartan_D_det (by decide)] at h
  apply isUnit_iff_dvd_one.mpr
  refine ⟨M.det, ?_⟩
  nlinarith

end Langlands.LinearAlgebra
