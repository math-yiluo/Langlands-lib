import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary
import Langlands.Representation.Derivative.LeibnizRankZeroGluing
import Langlands.Representation.Derivative.LeibnizPositiveGluing
import Langlands.Representation.Derivative.LeftMixedProductDerivativeProof
import Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof

/-!
# The all-rank actual general linear derivative Leibniz filtration

BZ77 Corollary 4.14(c), with the arbitrary-carrier rank-zero extension.
The positive-rank gluing premises are discharged by the published proofs of
the left and right mixed-product derivative formulas.
-/

namespace Langlands.Derivative

universe uF uV

/-- The actual natural Leibniz filtration in every rank and every valid order. -/
theorem generalLinearDerivativeLeibnizFiltration
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T := by
  intro ψ a b d hd
  cases d with
  | zero =>
      exact generalLinearDerivativeLeibnizFiltration_zero T ψ a b hd
  | succ d =>
      cases a with
      | zero =>
          exact generalLinearDerivativeLeibnizFiltration_left_zero T ψ b (d + 1) hd
      | succ m =>
          cases b with
          | zero =>
              exact generalLinearDerivativeLeibnizFiltration_right_zero T ψ (m + 1) (d + 1) hd
          | succ n =>
              exact generalLinearDerivativeLeibnizFiltration_pos T
                (leftMixedProductDerivativeIso.{uF, uV} F T)
                (leftMixedProductDerivativeVanishing.{uF, uV} F T)
                (rightMixedProductDerivativeFiltration.{uF, uV} F T)
                ψ m n (d + 1) ⟨Nat.succ_pos d, hd⟩

end Langlands.Derivative
