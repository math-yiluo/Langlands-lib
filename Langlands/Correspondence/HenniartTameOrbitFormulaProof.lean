import Langlands.Correspondence.HenniartTameOrbitCount
import Langlands.Correspondence.HenniartTameWeilFieldsProof

/-!
# The orbit formula for wild inertia orbits: proof
-/

namespace Langlands.Henniart

universe uK uW

/-- **Orbit formula**, `WeilTameOrbitFormulaStatement`: under its hypotheses on `J`, `m` and `φ`,
`C_K(p^r m, j)` is `q_K - 1` times the number of inertia orbits of tame wild classes that are
stable under conjugation by `φ`. -/
theorem weilTameOrbitFormula : WeilTameOrbitFormulaStatement.{uK, uW} :=
  weilTameOrbitFormula_of_parametrization tameWeilFrobeniusParametrization.{uK}

end Langlands.Henniart
