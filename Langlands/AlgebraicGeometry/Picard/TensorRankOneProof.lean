import Langlands.AlgebraicGeometry.Picard.TensorRankOneStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Local rank one of tensor powers of line bundles -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- Every nonnegative actual tensor power of a line bundle is locally free of rank one. -/
theorem tensorPow_isLocallyFreeRankOne :
    TensorPowLocallyFreeRankOneStatement.{u} := by
  intro X L n
  induction n with
  | zero => exact (LineBundle.trivial X).property
  | succ n ih => exact L.property.tensor pullbackTensorComparisonIsIso ih

end Langlands.AlgebraicGeometry.Picard
