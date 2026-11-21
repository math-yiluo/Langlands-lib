import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ProjectedDiscreteCoefficients
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalLevelAveraging
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSchwartzCentralConvergenceProof

/-! # Same-level lifting from the full cuspidal coefficient equality -/

universe u uV

namespace Langlands.HarishChandraSchwartz

open Langlands.GroupScheme Langlands.Plancherel MeasureTheory
open scoped CategoryTheory.MonObj

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The lower inclusion at the enlarged equality universe implies the lower
inclusion at the independent representation-carrier universe. -/
theorem RationalCuspidalDiscreteCoefficientLowerInclusionStatement.of_lifted
    (hlower : RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, max u uV}) :
    RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu f hf
  exact hlower F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA mu χ hχ hu
    (discreteSeriesCentralCoefficientSpace_le_universeLift.{u, uV, u}
      (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center mu χ hf)

/-- Full coefficient equality yields the specified raw preimage at the same
compact open level. -/
def RationalCuspidalLiftingFromEqualityStatement : Prop :=
  RationalCuspidalDiscreteCoefficientStatement.{u, uV} →
    RationalCuspidalFixedCoefficientLiftingStatement.{u, uV}

/-- Apply carrier-universe transport, central convergence and two-sided
averaging to the lower inclusion of the full coefficient equality. -/
theorem rationalCuspidalLiftingFromEquality : RationalCuspidalLiftingFromEqualityStatement.{u, uV} := by
  intro heq
  have hlower : RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, max u uV} := by
    intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _ mu _ χ hχ hu
    exact (heq F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA mu χ hχ hu).ge
  exact hlower.of_lifted.fixedCoefficientLifting rationalSchwartzCentralConvergence

end Langlands.HarishChandraSchwartz
