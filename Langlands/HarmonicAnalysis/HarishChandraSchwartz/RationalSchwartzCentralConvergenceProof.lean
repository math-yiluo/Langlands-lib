import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterHeightProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceReductions

/-! # Actual central convergence of Schwartz functions

The proof of `RationalSchwartzCentralConvergenceStatement`: for every actual Schwartz function
`f ∈ C(G)`, every Haar measure on `A_G(F)` and every unitary character `χ` of `A_G(F)`, the
central integral `a ↦ χ(a)⁻¹ f(a g)` is absolutely convergent at every `g`. It combines the
published proof `rationalSplitCenterHeight` of the height properties of the split centre with the
reduction `RationalSplitCenterHeightStatement.schwartzCentralConvergence`.
-/

universe u

namespace Langlands.HarishChandraSchwartz

/-- **Central convergence for the actual Schwartz space** (the convergence of the projections
`p_χ` of Waldspurger VIII.4 on `C(G)`): the proposition
`RationalSchwartzCentralConvergenceStatement` holds. -/
theorem rationalSchwartzCentralConvergence :
    RationalSchwartzCentralConvergenceStatement.{u} :=
  rationalSplitCenterHeight.schwartzCentralConvergence

end Langlands.HarishChandraSchwartz
