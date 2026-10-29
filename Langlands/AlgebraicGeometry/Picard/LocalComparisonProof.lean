import Langlands.AlgebraicGeometry.Picard.LocalComparisonStatement
import Langlands.AlgebraicGeometry.Picard.LocallyFreeTensorInvertibleProof
import Langlands.AlgebraicGeometry.Picard.TensorInvertibleLocallyFreeRankOneProof

/-!
# Tensor-invertibility is equivalent to local rank one on schemes

The two published directional theorems prove the exact comparison for the
actual symmetric monoidal category of scheme-module sheaves.
-/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- An actual scheme-module sheaf is tensor-invertible if and only if it is
locally free of rank one. -/
theorem locallyFreeRankOneIffTensorInvertible
    (X : _root_.AlgebraicGeometry.Scheme.{u}) :
    LocallyFreeRankOneIffTensorInvertibleStatement X := by
  intro M
  exact ⟨tensorInvertibleLocallyFreeRankOne X M,
    locallyFreeRankOneTensorInvertible X M⟩

end Langlands.AlgebraicGeometry.Picard
