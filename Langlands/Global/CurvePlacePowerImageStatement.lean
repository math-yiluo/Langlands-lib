import Langlands.Global.NumberFieldPowerImageStatement

/-! # Non-open images of power maps on function-field adelic units -/

noncomputable section

universe u

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Conrad's example for a global function field: every power map of exponent at least
`2` and prime to the characteristic has non-open image on adelic units. -/
def CurvePlacePowerImageStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (n : ℕ), 2 ≤ n → ¬ ringChar k ∣ n →
      PowerImageNotOpen (CurvePlaceAdeleRing k F) n

end Langlands.Global
