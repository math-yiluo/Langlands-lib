import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermConvergenceReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermEstimateProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # The cuspidal kernel is cut out by vanishing of the standard constant terms

The proof of `RationalCuspidalVanishingComparisonStatement`: an actual Schwartz function lies in
the convergence-strengthened cuspidal submodule `rationalCuspidalSubmodule` if and only if all its
normalized constant terms along proper standard parabolics vanish
(`RationalStandardConstantTermsVanish`). It applies the reduction
`RationalConstantTermEstimateStatement.cuspidalVanishingComparison` to the published proofs
`rationalConstantTermEstimate` (Waldspurger, Proposition II.4.5 on actual points) and
`BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` (a special compact subgroup with
its simultaneous standard basis).
-/

universe u

namespace Langlands.HarishChandraSchwartz

/-- **The vanishing-only description of the actual cuspidal kernel**: the proposition
`RationalCuspidalVanishingComparisonStatement` holds. -/
theorem rationalCuspidalVanishingComparison :
    RationalCuspidalVanishingComparisonStatement.{u} :=
  rationalConstantTermEstimate.cuspidalVanishingComparison
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.HarishChandraSchwartz
