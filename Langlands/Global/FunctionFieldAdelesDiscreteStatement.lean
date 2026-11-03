import Langlands.Global.FunctionFieldAbsoluteValueAdeles

/-! # Discrete closed diagonals in actual function-field adelic rings -/

universe u

namespace Langlands.Global

/-- The actual full-field diagonals have discrete, closed images in both
function-field adelic presentations, with their existing subspace topologies. -/
def FunctionFieldAdelesDiscreteStatement : Prop :=
  (∀ (k F : Type u) [Field k] [PerfectField k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
      DiscreteTopology (curvePlaceAdeleDiagonal k F).range ∧
        IsClosed ((curvePlaceAdeleDiagonal k F).range : Set (CurvePlaceAdeleRing k F))) ∧
  (∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
      DiscreteTopology (realAbsoluteValueAdeleDiagonal k F).range ∧
        IsClosed ((realAbsoluteValueAdeleDiagonal k F).range :
          Set (RealAbsoluteValueAdeleRing k F)))

end Langlands.Global
