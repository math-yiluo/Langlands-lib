import Langlands.Global.AdelicFixedModelLocalProductTopology
import Langlands.Global.AdelicFixedModelCocone

/-! # Local hypotheses for actual fixed-model adelic openness -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open scoped Langlands.Global.FixedModelLocalProduct

/-- The function-field passage from local openness and eventual surjectivity
at each enlarged level to actual fixed-model adelic openness. -/
def CurvePlaceFixedModelAdeleOpenOfLocalStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    (∀ (T : AdelicLevelIndexAbove S) i, @IsOpenMap _ _
      (schemePointTopology (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i))
      (schemePointTopology (curvePlaceSIntegers k F S) Y (CurvePlaceLevelFactor k F T.val i))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f)) →
    (∀ T : AdelicLevelIndexAbove S, ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F T.val i) =>
        p ≫ f)) →
    @IsOpenMap _ _ (curvePlaceFixedModelAdelePointTopology k F S X)
      (curvePlaceFixedModelAdelePointTopology k F S Y)
      (fun p : CurvePlaceFixedModelAdelePoints k F S X => p ≫ f)

/-- The full number-field passage, retaining all original infinite factors. -/
def NumberFieldFixedModelAdeleOpenOfLocalStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    (∀ (T : AdelicLevelIndexAbove S) i, @IsOpenMap _ _
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i))
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) Y
        (NumberFieldLevelFactor K T.val i))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i) => p ≫ f)) →
    (∀ T : AdelicLevelIndexAbove S, ∀ᶠ i in Filter.cofinite, Function.Surjective
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (NumberFieldLevelFactor K T.val i) => p ≫ f)) →
    @IsOpenMap _ _ (numberFieldFixedModelAdelePointTopology K S X)
      (numberFieldFixedModelAdelePointTopology K S Y)
      (fun p : NumberFieldFixedModelAdelePoints K S X => p ≫ f)

/-- The actual arithmetic local-to-adelic openness reduction in both
characteristics. The local geometric inputs remain explicit hypotheses. -/
def AdelicModelOpenReductionStatement : Prop :=
  CurvePlaceFixedModelAdeleOpenOfLocalStatement.{u} ∧
    NumberFieldFixedModelAdeleOpenOfLocalStatement.{u}

end Langlands.Global
