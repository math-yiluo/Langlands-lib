import Langlands.Global.AdelicProjectiveModels
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.DiscreteSubset

/-! # The proper, nonclosed and nondiscrete rational projective image -/

noncomputable section

universe u

open Topology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The principal rational projective image over a global function field is
proper, nonclosed and nondiscrete in every positive dimension. -/
def CurvePlaceProjectiveRationalImageStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)) (n : ℕ), 0 < n →
    letI := curvePlaceProjectiveAdelePointTopology k F S n
    let d := fun p : RingPoint F (projectivePointScheme F n) F =>
      p.changeRing (Algebra.ofId F (CurvePlaceAdeleRing k F))
    ¬ Function.Surjective d ∧ ¬ IsClosed (Set.range d) ∧ ¬ IsDiscrete (Set.range d)

/-- The number-field assertion retains all infinite and finite local factors. -/
def NumberFieldProjectiveRationalImageStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K)) (n : ℕ), 0 < n →
    letI := numberFieldProjectiveAdelePointTopology K S n
    let d := fun p : RingPoint K (projectivePointScheme K n) K =>
      p.changeRing (Algebra.ofId K (Adeles K))
    ¬ Function.Surjective d ∧ ¬ IsClosed (Set.range d) ∧ ¬ IsDiscrete (Set.range d)

/-- The proper-subset, nonclosedness and nondiscreteness conclusions of
Conrad Example 4.3 for the actual arithmetic adelic point topology. -/
def AdelicProjectiveRationalImageStatement : Prop :=
  CurvePlaceProjectiveRationalImageStatement.{u} ∧
    NumberFieldProjectiveRationalImageStatement.{u}

end Langlands.Global
