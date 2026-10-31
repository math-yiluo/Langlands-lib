import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.AdjacentSwapProof
import Langlands.Representation.Filtration.JordanHolderComparisonProof

/-! Factor matching for associated irreducible cuspidal data in arbitrary block
rank, from the adjacent block-swap step and factor-matching transitivity. -/

namespace Langlands.CuspidalSupport

universe uF uV uW

/-- Associated irreducible cuspidal data have normalized inductions with the
same Jordan–Hölder factors, including multiplicities, in every block rank. -/
theorem associatedCuspidalInductionFactorsTheorem :
    AssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW} := by
  intro p _ F T n hn
  exact associatedCuspidalInductionFactors_of_adjacent F T n
    (adjacentBlockSwapCuspidalInductionFactorsTheorem.{uF, uV, uV} p F T n hn)
    (adjacentBlockSwapCuspidalInductionFactorsTheorem.{uF, uV, uW} p F T n hn)
    (fun A A' A'' => haveSameJordanHolderFactors_trans ℂ _ A A' A'')
    (fun A A' A'' => haveSameJordanHolderFactors_trans ℂ _ A A' A'') hn

end Langlands.CuspidalSupport
