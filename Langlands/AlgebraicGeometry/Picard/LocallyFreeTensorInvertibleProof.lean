import Langlands.AlgebraicGeometry.Picard.LocalComparisonDirections
import Langlands.AlgebraicGeometry.Picard.DualEvaluationIsoProof

open CategoryTheory

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Every locally free rank-one module sheaf on a scheme has its actual
internal-Hom dual as a tensor inverse. -/
theorem locallyFreeRankOneTensorInvertible
    (X : _root_.AlgebraicGeometry.Scheme.{u}) :
    LocallyFreeRankOneTensorInvertibleStatement X := by
  intro M hM
  let := locallyFreeRankOneDualEvaluationIsIso X M hM
  exact ⟨Langlands.Scheme.Modules.dual M,
    ⟨asIso (Langlands.Scheme.Modules.dualMonoidalEval M)⟩⟩

end Langlands.AlgebraicGeometry.Picard
