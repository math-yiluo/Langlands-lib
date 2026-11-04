import Langlands.Global.AdelicFixedModelCocone
import Mathlib.NumberTheory.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Local compactness of actual full-adele model points -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Actual full-adele points of function-field models with finite constants. -/
def CurvePlaceFixedModelLocalCompactnessStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := curvePlaceFixedModelAdelePointTopology k F S X
    LocallyCompactSpace (CurvePlaceFixedModelAdelePoints k F S X) ∧
    (∀ [IsSeparated X.hom],
      T2Space (CurvePlaceFixedModelAdelePoints k F S X))

/-- Actual full number-field adele points, retaining every infinite completion. -/
def NumberFieldFixedModelLocalCompactnessStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := numberFieldFixedModelAdelePointTopology K S X
    LocallyCompactSpace (NumberFieldFixedModelAdelePoints K S X) ∧
    (∀ [IsSeparated X.hom],
      T2Space (NumberFieldFixedModelAdelePoints K S X))

/-- Finite-type arithmetic models have locally compact full-adele points;
separated models have Hausdorff full-adele points. -/
def AdelicFixedModelLocalCompactnessStatement : Prop :=
  CurvePlaceFixedModelLocalCompactnessStatement.{u} ∧
    NumberFieldFixedModelLocalCompactnessStatement.{u}

end Langlands.Global
