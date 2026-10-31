import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionReduction
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof

/-! Admissibility and finite length of actual refined cuspidal induction. -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- Actual refined induction of irreducible Levi-cuspidal data is admissible,
has finite group-algebra length, and admits an actual finite composition series. -/
theorem refinedCuspidalInductionFiniteLength :
    RefinedCuspidalInductionFiniteLengthStatement.{uF, uV} :=
  refinedCuspidalInductionReductionClause_holds.{uF, uV}
    (fun _ _ F T n _ => cuspidalInductionLength.{uF, uV} F T n)

end Langlands.CuspidalSupport
