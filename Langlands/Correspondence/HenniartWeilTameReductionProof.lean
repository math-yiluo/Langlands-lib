import Langlands.Correspondence.HenniartWeilTameReductionFromAveragingProof
import Langlands.Correspondence.HenniartWeilTameAveragingFromOrbitFormulasProof
import Langlands.Correspondence.HenniartTameWeilFieldsProof
import Langlands.Correspondence.HenniartTameOrbitFormulaProof
import Langlands.Correspondence.HenniartTameFieldFixedPointProof

/-!
# The truncated tame reduction of the Weil-side count

A proof of `WeilTameReductionStatement` (Koch 1984, Satz 4, in the truncated form of the
numerical LLC route): the fixed-cutoff tame average, assembled from the Frobenius coset
parametrization, the orbit formula and the fixed-point formula, gives the truncated reduction.
-/

namespace Langlands.Henniart

/-- The truncated tame reduction from rank `p ^ r` to rank `p ^ r * m`. -/
theorem weilTameReduction.{uK, uW} : WeilTameReductionStatement.{uK, uW} :=
  weilTameReductionFromAveraging.{uK, uW}
    (weilTameAveragingFromOrbitFormulas.{uK, uW} tameWeilFrobeniusParametrization.{uK}
      weilTameOrbitFormula.{uK, uW} weilTameFieldFixedPoint.{uK, uW})

end Langlands.Henniart
