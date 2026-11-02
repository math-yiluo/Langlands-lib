import Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.NumberTheory.FunctionField

/-! # Finite poles on actual function-field curve places -/

universe u

namespace Langlands.Global

/-- Every function-field element is integral at all but finitely many concrete curve places. -/
def CurvePlaceFinitePolesStatement : Prop :=
  ∀ (k F : Type u) [Field k] [PerfectField k] [Field F]
    [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F], ∀ x : F,
      {v : AlgebraicCurve.Place k F | x ∉ v.toValuationSubring}.Finite

end Langlands.Global
