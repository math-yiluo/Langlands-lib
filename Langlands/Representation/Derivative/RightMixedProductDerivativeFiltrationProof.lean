import Langlands.Representation.Derivative.RightMixedProductZeroRank
import Langlands.Representation.Derivative.RightMixedProductDerivativePositive
import Langlands.Representation.Derivative.MirabolicMinusExactnessProof
import Langlands.Representation.Derivative.MirabolicProductMinusRightPsi
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhi
import Langlands.Representation.Derivative.LeftMixedProductDerivativeProof

/-!
# BZ77 4.14(b): the right mixed-product derivative filtration

Dispatch on the `GL` rank: `k = 0` is the internal arbitrary-carrier extension
`rightMixedProductDerivativeFiltration_zero`; positive `k` is
`RightMixedDerivative.filtration_pos`, whose premises are discharged by the
published proofs of BZ77 4.13(c), 4.14(a) and minus exactness.
-/

namespace Langlands.Derivative

universe uF uV

/-- BZ77 4.14(b), with the internal `k = 0` extension: the actual finite natural
filtration of every derivative of every right mixed product. -/
theorem rightMixedProductDerivativeFiltration
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    RightMixedProductDerivativeFiltrationStatement.{uF, uV} F T := by
  intro ψ k
  cases k with
  | zero => exact rightMixedProductDerivativeFiltration_zero T ψ
  | succ k =>
    exact RightMixedDerivative.filtration_pos T ψ
      (MirabolicProductMinus.rightPsiCompatibility.{uF, uV} T)
      (MirabolicProductMinus.rightPhiShortExact.{uF, uV} T)
      (leftMixedProductDerivativeIso.{uF, uV} F T)
      (leftMixedProductDerivativeVanishing.{uF, uV} F T)
      (Mirabolic.minusExactness.{uF, max uF uV} F T) k

end Langlands.Derivative
