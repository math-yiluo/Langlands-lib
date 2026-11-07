import Langlands.AlgebraicGeometry.UniformLangWeilStatement
import Langlands.Global.AdelicFixedModelLocalProductTopology
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Almost-all native level surjectivity without a common fibre dimension -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped Langlands.Global.FixedModelLocalProduct

/-- Smooth geometrically connected models have cofinally surjective maps on
the actual function-field level factors, with no common dimension premise. -/
def CurvePlaceLevelComponentSurjectivityStatement : Prop :=
  UniformLangWeilStatement.{u} →
    ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
      [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
      (S : Finset (AlgebraicCurve.Place k F))
      (B Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      (f : Y ⟶ B),
      LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left) →
      CompactSpace B.left → Smooth f.left → IsSeparated f.left →
      QuasiCompact f.left → GeometricallyConnected f.left →
      ∀ T : AdelicLevelIndexAbove S, ∀ᶠ i in Filter.cofinite, Function.Surjective
        (fun p : RingPoint (curvePlaceSIntegers k F S) Y
          (CurvePlaceLevelFactor k F T.val i) => p ≫ f)

/-- The corresponding assertion for all original number-field factors,
including the infinite places in each full level. -/
def NumberFieldLevelComponentSurjectivityStatement : Prop :=
  UniformLangWeilStatement.{u} →
    ∀ (K : Type u) [Field K] [NumberField K]
      (S : Finset (FinitePlace K))
      (B Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
      (f : Y ⟶ B),
      LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left) →
      CompactSpace B.left → Smooth f.left → IsSeparated f.left →
      QuasiCompact f.left → GeometricallyConnected f.left →
      ∀ T : AdelicLevelIndexAbove S, ∀ᶠ i in Filter.cofinite, Function.Surjective
        (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (NumberFieldLevelFactor K T.val i) => p ≫ f)

/-- Actual cofinite surjectivity in both characteristics, allowing dimensions
to vary among the target's connected components. -/
def AdelicLevelComponentSurjectivityStatement : Prop :=
  CurvePlaceLevelComponentSurjectivityStatement.{u} ∧
    NumberFieldLevelComponentSurjectivityStatement.{u}

end Langlands.Global
