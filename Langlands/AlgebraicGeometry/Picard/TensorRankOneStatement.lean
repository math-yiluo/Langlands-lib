import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # Local rank one of actual tensor powers of line bundles -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- Every nonnegative actual tensor power of a locally free rank-one module sheaf on a
scheme is again locally free of rank one. -/
def TensorPowLocallyFreeRankOneStatement : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X) (n : ℕ),
    IsLocallyFreeRankOne (tensorPow L.obj n)

end Langlands.AlgebraicGeometry.Picard
