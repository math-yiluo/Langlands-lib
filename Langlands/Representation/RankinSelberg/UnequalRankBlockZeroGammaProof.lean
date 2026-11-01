import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaAssembly
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof
import Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessProof

/-!
# The unequal-rank block-zero rational functional equation

The published analytic, continued-form and full Whittaker-type uniqueness
theorems discharge all inputs of the universal gamma assembly.
-/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- A single nonzero rational gamma function relates all actual coefficient
pairs at block zero, for the full published Whittaker-type scope. -/
theorem unequalRankBlockZeroGammaExistence {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankBlockZeroGammaExistenceStatement.{uF,uV,uW} F T n r :=
  UnequalRankBlockZeroGammaAssemblyInput.gammaExistence F T n r
    ⟨fun j k => unequalRankAnalytic.{uF,uV,uW} F T n j k,
      unequalRankBlockZeroContinuedForms.{uF,uV,uW} F T n r,
      unequalRankBilinearUniqueness.{uF,uV,uW} F T n r⟩

end Langlands.RankinSelberg
