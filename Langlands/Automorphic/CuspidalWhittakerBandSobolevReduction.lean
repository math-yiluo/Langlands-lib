import Langlands.Automorphic.CuspidalWhittakerBandSobolevEstimate
import Langlands.Automorphic.CuspidalWhittakerBandReduction

/-! # Actual cuspidal multiplicity one from compact Sobolev and comparison -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic

/-- The exact unrestricted multiplicity-one consequent, retaining both the
compact Sobolev estimate and analytic comparison as named open premises. -/
def CuspidalWhittakerBandSobolevReductionStatement : Prop :=
  OperatorCompactSobolevStatement.{u} →
    CuspidalWhittakerBandSobolevComparisonStatement.{u} →
      CuspidalOperatorMultiplicityOneStatement.{u}

set_option maxHeartbeats 1600000 in
/-- Compact Sobolev supplies the actual band-bound premise of the band
reduction; the analytic comparison remains an explicit open premise. -/
theorem cuspidalWhittakerBandSobolevReduction :
    CuspidalWhittakerBandSobolevReductionStatement.{u} := by
  intro hSobolev hComparison
  apply cuspidalWhittakerBandReduction _ hComparison
  intro F _ _ _ r T hT hL2 ψ hψ
  obtain ⟨χ, hχ, hTχ⟩ := hT
  exact cuspWhittakerBandBound_of_compactSobolev F T hSobolev χ hχ hTχ hL2 ψ hψ

end Langlands.Automorphic
