import Langlands.Global.AdelicFixedModelLocalProductTopology
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth openness at every actual adelic-level local factor -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open scoped Langlands.Global.FixedModelLocalProduct

/-- Smooth maps of the original curve-place models induce open maps at
all native completed field and completed integer factors at every level. -/
def CurvePlaceSmoothLocalPointOpenStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [Smooth f.left] (T : AdelicLevelIndexAbove S)
    (i : CurvePlaceLevelFactorIndex k F T.val),
    @IsOpenMap _ _
      (schemePointTopology (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i))
      (schemePointTopology (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F T.val i))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f)

/-- Smooth maps of the original number-field models induce open maps at
every infinite, supported finite field and outside integral factor. -/
def NumberFieldSmoothLocalPointOpenStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [Smooth f.left] (T : AdelicLevelIndexAbove S)
    (i : NumberFieldLevelFactorIndex K T.val),
    @IsOpenMap _ _
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i))
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) Y
        (NumberFieldLevelFactor K T.val i))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i) => p ≫ f)

/-- The local-openness input for the actual fixed-model adelic reduction,
in both characteristics and including every infinite number-field factor. -/
def AdelicSmoothLocalPointOpenStatement : Prop :=
  CurvePlaceSmoothLocalPointOpenStatement.{u} ∧
    NumberFieldSmoothLocalPointOpenStatement.{u}

end Langlands.Global
