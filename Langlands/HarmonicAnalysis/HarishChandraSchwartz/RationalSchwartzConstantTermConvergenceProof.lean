import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermConvergenceReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermEstimateProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Actual radical convergence of Schwartz functions

The proof of `RationalSchwartzConstantTermConvergenceStatement`: for every actual Schwartz
function `f ∈ C(G)`, every proper standard parabolic `P_J = M_J U_J`, every Haar measure on
`U_J(F)` and all `x, y ∈ G(F)`, the function `v ↦ f(x v y)` is integrable on `U_J(F)`. It applies
the reduction `RationalConstantTermEstimateStatement.schwartzConstantTermConvergence` to the
published proofs `rationalConstantTermEstimate` (Waldspurger, Proposition II.4.5 on actual points)
and `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` (a special compact subgroup with
its simultaneous standard basis).
-/

universe u

namespace Langlands.HarishChandraSchwartz

/-- **Radical convergence for the actual Schwartz space** (the convergence of the constant-term
integrals of Waldspurger III.6 on `C(G)`): the proposition
`RationalSchwartzConstantTermConvergenceStatement` holds. -/
theorem rationalSchwartzConstantTermConvergence :
    RationalSchwartzConstantTermConvergenceStatement.{u} :=
  rationalConstantTermEstimate.schwartzConstantTermConvergence
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.HarishChandraSchwartz
