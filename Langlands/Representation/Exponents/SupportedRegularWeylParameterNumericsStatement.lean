import Langlands.Representation.Exponents.PositiveRootParameterConeStatement

/-! Finite-coordinate adapters for the supported regular Weyl comparison. -/

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeRegularComparison
open scoped BigOperators

set_option autoImplicit false

/-- Weighted lifting, supported orthogonality, and preservation of the first
permutation when two independent one-sided cone comparisons are combined. -/
def SupportedRegularWeylParameterNumericsStatement : Prop :=
  (∀ (n : ℕ) (B : BlockShape n) (v : Fin B.length → ℝ),
    IsClosedPositiveRootCone (fun i => (B.size i : ℝ) * v i) →
    IsClosedPositiveRootCone (fun a => v (blockIndex B a))) ∧
  (∀ (n : ℕ) (B : BlockShape n) (Q : BlockRefinement B)
      (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
      (h : (B.flatten Q).flatten R = B.flatten S)
      (v : Fin ((B.flatten Q).flatten R).length → ℝ)
      (t : Fin B.length → ℝ),
    IsPositiveRootParameter (B.flatten Q) R v →
    IsClosedPositiveRootCone (fun a => (h ▸ v) (blockIndex (B.flatten S) a)) ∧
      (∑ a, (h ▸ v) (blockIndex (B.flatten S) a) * t (blockIndex B a)) = 0 ∧
      (StrictAnti t → Antitone (fun a => t (blockIndex B a)))) ∧
  (∀ (n : ℕ) (V1 V2 A1 A2 : Fin n → ℝ) (s r : Equiv.Perm (Fin n)),
    (∑ i, V1 i * A1 i) = 0 →
    (∑ i, V2 i * A2 i) = 0 →
    Antitone A1 →
    Antitone A2 →
    IsClosedPositiveRootCone (fun i => V1 (s.symm i)) →
    IsClosedPositiveRootCone (fun i => V2 (r.symm i)) →
    (∀ i, V1 (s.symm i) - A1 (s.symm i) = V2 i - A2 i) →
    (∀ i, V2 (r.symm i) - A2 (r.symm i) = V1 i - A1 i) →
    IsClosedPositiveRootCone V1 →
    (∀ i, V1 (s.symm i) = V2 i) ∧
      IsClosedPositiveRootCone (fun i => V2 (s i)))

end Langlands.Exponents
