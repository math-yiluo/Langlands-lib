import Langlands.Global.AdelicProjectiveModels
import Langlands.Global.AllPlaceSchemePoints
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Concrete projective adelic points as the full local product -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Actual projective adelic points over a global function field have the full
local product topology and form a compact Hausdorff space. -/
def CurvePlaceProjectiveComparisonStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)) (n : ℕ),
    letI := curvePlaceProjectiveAdelePointTopology k F S n
    letI := curvePlaceLocalPointTopology k F (projectivePointScheme F n)
    IsHomeomorph (curvePlaceAdelePointMap k F (projectivePointScheme F n)) ∧
      CompactSpace (CurvePlaceAdelePoints k F (projectivePointScheme F n)) ∧
      T2Space (CurvePlaceAdelePoints k F (projectivePointScheme F n))

/-- The number-field comparison includes every infinite and finite local factor. -/
def NumberFieldProjectiveComparisonStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K)) (n : ℕ),
    letI := numberFieldProjectiveAdelePointTopology K S n
    letI := numberFieldLocalPointTopology K (projectivePointScheme K n)
    IsHomeomorph (numberFieldAdelePointMap K (projectivePointScheme K n)) ∧
      CompactSpace (NumberFieldAdelePoints K (projectivePointScheme K n)) ∧
      T2Space (NumberFieldAdelePoints K (projectivePointScheme K n))

/-- The full-product and compact-Hausdorff conclusions of Conrad Example 4.3,
with the harmless dimension-zero extension included. -/
def AdelicProjectiveComparisonStatement : Prop :=
  CurvePlaceProjectiveComparisonStatement.{u} ∧ NumberFieldProjectiveComparisonStatement.{u}

end Langlands.Global
