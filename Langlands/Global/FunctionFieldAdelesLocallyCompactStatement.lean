import Langlands.Global.FunctionFieldAbsoluteValueAdeles

/-! # Local compactness for actual function-field adelic rings -/

universe u

namespace Langlands.Global

/-- Actual completed integer rings are compact, their completed fields are
locally compact, and the full adelic rings and all finite levels are locally
compact, over finite constants. -/
def FunctionFieldAdelesLocallyCompactStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F],
      (∀ v : AlgebraicCurve.Place k F,
        CompactSpace (curvePlaceCompletionIntegers v) ∧
          LocallyCompactSpace (curvePlaceCompletion v)) ∧
      LocallyCompactSpace (CurvePlaceAdeleRing k F) ∧
      (∀ S : Finset (AlgebraicCurve.Place k F),
        LocallyCompactSpace (curvePlaceAdeleLevel k F S)) ∧
      LocallyCompactSpace (RealAbsoluteValueAdeleRing k F) ∧
      (∀ S : Finset (RealAbsoluteValuePlace (F := F)),
        LocallyCompactSpace (realAbsoluteValueAdeleLevel k F S))

end Langlands.Global
