import Langlands.Representation.Derivative.Homogeneity

/-! The `GL_(N+1)` derivative of positive order `k` is the
mirabolic derivative of order `k` of the restriction to `P_(N+1)`. -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private theorem restriction_derivative_cast (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m j N : ℕ)
    (h₁ : N + 1 = m + j + 1) (h₂ : N = m + j) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h₁ ⋙ generalLinearRestriction T (m + j) ⋙
        mirabolicDerivative T ψ m j =
      generalLinearRestriction T N ⋙ mirabolicRankCast T h₂ ⋙ mirabolicDerivative T ψ m j := by
  subst h₂
  rfl

/-- For `0 < k ≤ N + 1`, the `k`-th derivative of `GL_(N+1)` is restriction to
`P_(N+1)` followed by the mirabolic derivative of order `k`. -/
theorem generalLinearDerivative_eq_restriction_comp (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k ≤ N + 1)
    (hk' : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    generalLinearDerivative.{uF, uV} T ψ (N + 1) k hk =
      generalLinearRestriction T N ⋙ mirabolicDerivativeOfOrder T ψ N k hk' := by
  cases k with
  | zero => exact absurd hk'.1 (Nat.lt_irrefl 0)
  | succ j =>
    exact restriction_derivative_cast T ψ (N + 1 - (j + 1)) j N
      (rank_eq_of_succ_le hk) (mirabolic_rank_eq_of_order hk')

theorem generalLinearDerivative_obj_eq_restriction (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k ≤ N + 1)
    (hk' : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      (generalLinearDerivative T ψ (N + 1) k hk).obj A =
        (mirabolicDerivativeOfOrder T ψ N k hk').obj ((generalLinearRestriction T N).obj A) := by
  intro A
  rw [generalLinearDerivative_eq_restriction_comp T ψ N k hk hk']
  rfl

end Langlands.Derivative
