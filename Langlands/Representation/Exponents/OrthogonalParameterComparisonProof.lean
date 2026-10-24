import Langlands.Representation.Exponents.OrthogonalParameterComparisonStatement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Proof of the internal orthogonal parameter comparison. -/

namespace Langlands.Exponents

universe u

/-- The common difference has zero squared norm, so both pairs coincide. -/
theorem orthogonalParameterComparison : OrthogonalParameterComparisonStatement.{u} := by
  intro E _ _ x₁ y₁ x₂ y₂ hdiff h₁ h₂ h₁₂ h₂₁
  have hd : x₁ - x₂ = y₁ - y₂ := by
    calc
      x₁ - x₂ = (x₁ - y₁) - (x₂ - y₂) + (y₁ - y₂) := by abel
      _ = y₁ - y₂ := by rw [hdiff]; simp
  have hnonpos : inner ℝ (x₁ - x₂) (x₁ - x₂) ≤ 0 := by
    calc
      inner ℝ (x₁ - x₂) (x₁ - x₂) =
          inner ℝ (x₁ - x₂) (y₁ - y₂) := congrArg (inner ℝ (x₁ - x₂)) hd
      _ = -inner ℝ x₁ y₂ - inner ℝ y₁ x₂ := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right, h₁, h₂,
          real_inner_comm x₂ y₁]
        ring
      _ ≤ 0 := by linarith
  have hz : x₁ - x₂ = 0 :=
    (inner_self_eq_zero (𝕜 := ℝ)).mp (le_antisymm hnonpos (real_inner_self_nonneg))
  exact ⟨sub_eq_zero.mp hz, sub_eq_zero.mp (hd.symm.trans hz)⟩

end Langlands.Exponents
