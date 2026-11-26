import Langlands.Global.CurvePlaceAdeleRing
import Mathlib.NumberTheory.FunctionField

/-! # A single prescribed pole in a global function field -/

universe u

namespace Langlands.Global

/-- Every actual place admits a function with a pole only at that place. -/
def CurvePlaceSinglePoleStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (v : AlgebraicCurve.Place k F),
    ∃ f : F, f ∉ v.toValuationSubring ∧
      ∀ w : AlgebraicCurve.Place k F, w ≠ v → f ∈ w.toValuationSubring

end Langlands.Global
