import Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof
import Langlands.Global.Factors.CuspidalSelfPairContinuationProof

/-!
# Absolute convergence of cuspidal pair Euler products
-/

namespace Langlands.Global

universe u uQ

/-- Jacquet–Shalika I, Theorem (5.3), obtained by applying the absolute
convergence reduction to the self-pair continuation theorem. -/
theorem cuspidalPairAbsoluteConvergence :
    CuspidalPairAbsoluteConvergenceStatement.{u, uQ} :=
  cuspidalPairAbsoluteConvergenceReduction.{u, uQ} cuspidalSelfPairContinuation.{u, uQ}

end Langlands.Global
