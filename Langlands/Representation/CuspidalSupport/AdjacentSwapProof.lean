import Langlands.Representation.CuspidalSupport.AdjacentMatchingAssembly
import Langlands.Representation.CuspidalSupport.TwoBlockAssociationProof
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof

/-! Factor matching for normalized cuspidal induction under an adjacent block swap. -/

namespace Langlands.CuspidalSupport

universe uF uV uW

/-- Associated irreducible cuspidal data related by a minimal adjacent block
swap have normalized inductions with the same Jordan–Hölder factors,
including multiplicities. -/
theorem adjacentBlockSwapCuspidalInductionFactorsTheorem :
    AdjacentBlockSwapCuspidalInductionFactorsTheorem.{uF, uV, uW} :=
  adjacentBlockSwap_of_twoBlock_and_length.{uF, uV, uW}
    twoBlockAssociatedCuspidalInductionFactors.{uF, uV, uV}
    (fun _ _ F T n => cuspidalInductionLength.{uF, uV} F T n)

end Langlands.CuspidalSupport
