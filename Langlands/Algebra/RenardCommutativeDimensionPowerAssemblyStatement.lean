import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace Langlands.Renard

/-- Renard C.I: convexity and finite-sum comparison for the exact source power. -/
def CommutativeDimensionPowerAssemblyStatement : Prop :=
  ∀ l : ℕ, 1 ≤ l →
    let r : ℝ := 2 - Real.rpow 2 (1 - (l : ℝ))
    1 ≤ r ∧
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => Real.rpow x r) ∧
      ∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 ≤ x i) →
        (∑ i, Real.rpow (x i) r) ≤ Real.rpow (∑ i, x i) r

end Langlands.Renard
