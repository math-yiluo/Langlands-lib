import Langlands.Global.AdelicProjectiveModels

/-! # Density of rational points in actual adelic projective space -/

noncomputable section

universe u

open Topology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Rational projective points are dense for the actual arithmetic adelic topology
over every global function field, including inseparable finite presentations. -/
def CurvePlaceProjectiveRationalDensityStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)) (n : ℕ),
    letI := curvePlaceProjectiveAdelePointTopology k F S n
    DenseRange (fun p : RingPoint F (projectivePointScheme F n) F =>
      p.changeRing (Algebra.ofId F (CurvePlaceAdeleRing k F)))

/-- Number-field rational projective points are dense in the arithmetic adelic
space retaining every infinite and finite local factor. -/
def NumberFieldProjectiveRationalDensityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K)) (n : ℕ),
    letI := numberFieldProjectiveAdelePointTopology K S n
    DenseRange (fun p : RingPoint K (projectivePointScheme K n) K =>
      p.changeRing (Algebra.ofId K (Adeles K)))

/-- The rational-point density conclusion of Conrad Example 4.3, with its
harmless dimension-zero extension. -/
def AdelicProjectiveRationalDensityStatement : Prop :=
  CurvePlaceProjectiveRationalDensityStatement.{u} ∧
    NumberFieldProjectiveRationalDensityStatement.{u}

end Langlands.Global
