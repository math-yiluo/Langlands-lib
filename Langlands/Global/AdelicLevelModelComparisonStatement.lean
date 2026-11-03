import Langlands.Global.AdelicLevelModelPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeCoordinates

/-! # Comparison targets for actual adelic-level model points -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Separate geometric hypotheses for the actual curve-place level point map. -/
def CurvePlaceLevelModelComparisonStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))),
    (∀ [QuasiSeparatedSpace X.left],
      Function.Injective (curvePlaceLevelModelPointMap k F S X)) ∧
    (∀ [IsAffine X.left],
      Function.Surjective (curvePlaceLevelModelPointMap k F S X)) ∧
    (∀ [CompactSpace X.left],
      Function.Surjective (curvePlaceLevelModelPointMap k F S X)) ∧
    (∀ [CompactSpace X.left] [QuasiSeparatedSpace X.left],
      Function.Bijective (curvePlaceLevelModelPointMap k F S X)) ∧
    (∀ [IsAffine X.left],
      IsHomeomorph (curvePlaceLevelModelPointMap k F S X))

/-- Separate geometric hypotheses for the actual full number-field level point map. -/
def NumberFieldLevelModelComparisonStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    (∀ [QuasiSeparatedSpace X.left],
      Function.Injective (numberFieldLevelModelPointMap K S X)) ∧
    (∀ [IsAffine X.left],
      Function.Surjective (numberFieldLevelModelPointMap K S X)) ∧
    (∀ [CompactSpace X.left],
      Function.Surjective (numberFieldLevelModelPointMap K S X)) ∧
    (∀ [CompactSpace X.left] [QuasiSeparatedSpace X.left],
      Function.Bijective (numberFieldLevelModelPointMap K S X)) ∧
    (∀ [IsAffine X.left],
      IsHomeomorph (numberFieldLevelModelPointMap K S X))

/-- The actual arithmetic level comparisons in both characteristics. -/
def AdelicLevelModelComparisonStatement : Prop :=
  CurvePlaceLevelModelComparisonStatement.{u} ∧
    NumberFieldLevelModelComparisonStatement.{u}

end Langlands.Global
