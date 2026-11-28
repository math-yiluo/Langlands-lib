import Langlands.Analysis.Meromorphic.ContinuationPrincipleHolomorphicProof
import Langlands.Global.AdelicEisensteinAnalyticSystemReduction
import Langlands.Global.AdelicEisensteinCommonGrowthProof
import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicEisensteinSystemDominationReduction
import Langlands.Global.AdelicLocalFinitenessSolutionAutomorphyProof
import Langlands.Global.AdelicParabolicCuspidalVanishingProof
import Langlands.Global.AdelicPositiveTorusSplitComponentProof

universe u

namespace Langlands.Global

/-- The induced Harish-Chandra equations and the cuspidal test system imply
meromorphic continuation of Eisenstein series. -/
theorem eisensteinMeromorphicContinuation_of_induced_of_cuspidalTests
    (hHC : InducedHarishChandraEquationsStatement.{u})
    (hCusp : EisensteinCuspidalTestSystemStatement.{u}) :
    EisensteinMeromorphicContinuationStatement.{u} :=
  eisensteinMeromorphicContinuation_of_analyticSystem
    Langlands.Analysis.Meromorphic.meromorphicContinuationHolomorphic
    (eisensteinAnalyticSystem_of_localFiniteness_of_domination uniformGrowthLocalFiniteness
      (eisensteinSystemDomination_of (eisensteinHarishChandraEquations_of_induced hHC)
        hCusp eisensteinCommonGrowth parabolicCuspidalVanishing
        localFinitenessSolutionAutomorphy positiveTorusSplitComponent))

end Langlands.Global
