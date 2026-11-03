import Langlands.Global.AdelicLevelModelPoints
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.NumberTheory.FunctionField

/-! # Finite-type comparison targets for actual adelic-level model points -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Local finite type gives injectivity, and finite type gives bijectivity,
for models over the actual function-field S-integer ring. -/
def CurvePlaceFiniteTypeLevelModelComparisonStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))),
    (∀ [LocallyOfFiniteType X.hom],
      Function.Injective (curvePlaceLevelModelPointMap k F S X)) ∧
    (∀ [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
      Function.Bijective (curvePlaceLevelModelPointMap k F S X))

/-- Local finite type gives injectivity, and finite type gives bijectivity,
for models over the actual number-field S-integer ring. -/
def NumberFieldFiniteTypeLevelModelComparisonStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    (∀ [LocallyOfFiniteType X.hom],
      Function.Injective (numberFieldLevelModelPointMap K S X)) ∧
    (∀ [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
      Function.Bijective (numberFieldLevelModelPointMap K S X))

/-- Actual finite-type level comparisons in both characteristics. -/
def AdelicFiniteTypeLevelModelComparisonStatement : Prop :=
  CurvePlaceFiniteTypeLevelModelComparisonStatement.{u} ∧
    NumberFieldFiniteTypeLevelModelComparisonStatement.{u}

end Langlands.Global
