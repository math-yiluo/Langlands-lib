import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The finite counting and integer parameter step of Stepanov's method

This proposition turns bounds on two auxiliary polynomials into a square-root
estimate for the sum of an arbitrary finite fibre-count function.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

open scoped BigOperators

/-- The counting part of Schmidt's method, on an arbitrary finite fibre-count function.
The hypothesis supplies auxiliary polynomials for every admissible integer parameter.
Their construction is a separate algebraic obligation. -/
def StepanovCountingStatement : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (r : F → ℕ) (m n : ℕ),
    2 ≤ n → n ≤ m →
    9 * (m + 1) ^ 2 * (n + 1) ^ 2 < Fintype.card F →
    (∀ M : ℕ, 0 < M →
      M ^ 2 * (n ^ 2 + 1) + (M + m) * n ^ 2 < Fintype.card F →
      M * n ≤ Fintype.card F →
      ∃ (s : Finset F) (h₁ h₂ : Polynomial F),
        Fintype.card F < s.card + 2 * m * n ∧
        (∀ x : F, r x ≤ n) ∧
        h₁.natDegree < Fintype.card F * (M + (2 * m * (n - 1) + 1)) ∧
        h₂.natDegree < Fintype.card F * ((n - 1) * M + (2 * m * (n - 1) + 1)) ∧
        ∀ x ∈ s,
          M * r x ≤ h₁.rootMultiplicity x ∧
          M * (n - r x) ≤ h₂.rootMultiplicity x) →
    |((∑ x : F, r x : ℕ) : ℝ) - (Fintype.card F : ℝ)| <
      2 * (m * n ^ 2 : ℕ) * Real.sqrt (Fintype.card F)

end Langlands.AlgebraicGeometry.LangWeil
