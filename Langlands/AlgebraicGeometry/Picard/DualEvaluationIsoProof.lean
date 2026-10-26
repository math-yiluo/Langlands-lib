import Langlands.AlgebraicGeometry.Picard.DualEvaluationIsoStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation

/-! # The canonical monoidal dual evaluation of a locally free rank-one sheaf -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- The canonical dual evaluation is invertible for every locally free rank-one
module sheaf on an arbitrary scheme. -/
theorem locallyFreeRankOneDualEvaluationIsIso
    (X : _root_.AlgebraicGeometry.Scheme.{u}) :
    LocallyFreeRankOneDualEvaluationIsIsoStatement X := by
  intro M hM
  have := Langlands.Scheme.Modules.isIso_dualTensorEval hM
  unfold Langlands.Scheme.Modules.dualMonoidalEval
  infer_instance

end Langlands.AlgebraicGeometry.Picard
