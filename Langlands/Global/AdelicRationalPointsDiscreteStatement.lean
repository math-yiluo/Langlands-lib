import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeCoefficientStatements
import Langlands.Global.NumberFieldAdeleLevel
import Langlands.Global.CurvePlaceAdeleDiagonal

/-! # Discreteness of rational and integral affine points in adelic points -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- With the discrete topology on `R`, the coefficient map from `R`-points to
`T`-points of every finite-type affine scheme is an embedding onto a discrete subset. -/
def AffineDiscreteCoefficientConclusion (R T : Type u) [CommRing R] [CommRing T]
    [Algebra R T] [TopologicalSpace T] : Prop :=
  letI : TopologicalSpace R := ⊥
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] [LocallyOfFiniteType X.hom],
    IsEmbedding (RingPoint.changeRing (X := X) (Algebra.ofId R T)) ∧
      DiscreteTopology (Set.range (RingPoint.changeRing (X := X) (Algebra.ofId R T)))

/-- An injective structure map with discrete image gives the point conclusion. -/
def AffineDiscreteSubringProperty (R T : Type u) [CommRing R] [CommRing T]
    [Algebra R T] [TopologicalSpace T] : Prop :=
  Function.Injective (algebraMap R T) →
    DiscreteTopology (Set.range (algebraMap R T)) →
      AffineDiscreteCoefficientConclusion R T

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Rational points of a number field in points over its full adele ring. -/
def NumberFieldRationalPointsDiscreteStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    AffineDiscreteCoefficientConclusion K (Adeles K)

/-- `S`-integral points in points over the full adelic level of `S`. -/
def NumberFieldIntegralPointsDiscreteStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    AffineDiscreteCoefficientConclusion ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevel K S)

/-- Rational points of a function field in points over its curve-place adeles. -/
def CurvePlaceRationalPointsDiscreteStatement : Prop :=
  ∀ (k F : Type u) [Field k] [PerfectField k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
    AffineDiscreteCoefficientConclusion F (CurvePlaceAdeleRing k F)

/-- Outside-`S` integral points in points over the curve-place adelic level of `S`. -/
def CurvePlaceIntegralPointsDiscreteStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    AffineDiscreteCoefficientConclusion (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevel k F S)

/-- Conrad's discreteness of rational and integral affine points, with the
general discrete-subring transfer. -/
def AdelicRationalPointsDiscreteStatement : Prop :=
  (∀ (R T : Type u) [CommRing R] [CommRing T] [Algebra R T] [TopologicalSpace T],
      AffineDiscreteSubringProperty R T) ∧
    NumberFieldRationalPointsDiscreteStatement.{u} ∧
    NumberFieldIntegralPointsDiscreteStatement.{u} ∧
    CurvePlaceRationalPointsDiscreteStatement.{u} ∧
    CurvePlaceIntegralPointsDiscreteStatement.{u}

end Langlands.Global
