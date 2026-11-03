import Langlands.Global.FunctionFieldAbsoluteValueAdeles
import Mathlib.Topology.Bases

/-! # Countable bases for actual function-field adelic rings -/

universe u

namespace Langlands.Global

/-- The actual global field and its place sets are countable; all completed
local factors, both adelic rings and all finite levels are second countable. -/
def FunctionFieldAdelesSecondCountableStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F],
      Countable F ∧
      Countable (AlgebraicCurve.Place k F) ∧
      Countable (RealAbsoluteValuePlace (F := F)) ∧
      (∀ v : AlgebraicCurve.Place k F, SecondCountableTopology (curvePlaceCompletion v)) ∧
      (∀ q : RealAbsoluteValuePlace (F := F),
        SecondCountableTopology (realAbsoluteValuePlaceCompletion q)) ∧
      SecondCountableTopology (CurvePlaceAdeleRing k F) ∧
      (∀ S : Finset (AlgebraicCurve.Place k F),
        SecondCountableTopology (curvePlaceAdeleLevel k F S)) ∧
      SecondCountableTopology (RealAbsoluteValueAdeleRing k F) ∧
      (∀ S : Finset (RealAbsoluteValuePlace (F := F)),
        SecondCountableTopology (realAbsoluteValueAdeleLevel k F S))

end Langlands.Global
