import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Langlands.Renard

/-- Renard C.I: normalization and the numerical inequality excluding a strict counterexample. -/
def CommutativeDimensionNumericalContradictionStatement : Prop :=
  ∀ (l k : ℕ), 1 ≤ l → 2 ≤ k →
    let ε : ℝ := 1 - (l : ℝ)
    let m : ℝ := (k : ℝ)
    let d : ℝ := Real.rpow 2 ε
    let r : ℝ := 2 - d
    let x : ℝ := Real.rpow m (-d)
    let D : ℝ := Real.rpow m r
    let P : ℝ := Real.rpow m (2 - Real.rpow 2 (ε + 1))
    1 ≤ r ∧
      0 < 1 - x ∧
      1 - x < 1 ∧
      (Real.rpow (m - D / m) r + P) / D =
        Real.rpow (1 - x) r + x ∧
      Real.rpow (1 - x) r ≤ 1 - x ∧
      Real.rpow (m - D / m) r + P ≤ D

end Langlands.Renard
