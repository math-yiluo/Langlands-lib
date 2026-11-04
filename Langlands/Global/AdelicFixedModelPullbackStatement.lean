import Langlands.Global.AdelicFixedModelCocone
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbackPoints
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.NumberTheory.FunctionField

/-! # Pullbacks of actual full-adele fixed-model point spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- For finite-type curve-place models over a separated base model, the actual
full-adele pullback comparison is a homeomorphism for the final topologies. -/
def CurvePlaceFixedModelPullbackStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g), IsLimit c →
    letI : TopologicalSpace (CurvePlaceFixedModelAdelePoints k F S X) :=
      curvePlaceFixedModelAdelePointTopology k F S X
    letI : TopologicalSpace (CurvePlaceFixedModelAdelePoints k F S Y) :=
      curvePlaceFixedModelAdelePointTopology k F S Y
    @IsHomeomorph
      (CurvePlaceFixedModelAdelePoints k F S c.pt)
      {q : CurvePlaceFixedModelAdelePoints k F S X ×
        CurvePlaceFixedModelAdelePoints k F S Y // q.1 ≫ f = q.2 ≫ g}
      (curvePlaceFixedModelAdelePointTopology k F S c.pt) inferInstance
      (affineSchemePullbackPointComparison
        (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) c)

/-- For finite-type number-field models over a separated base model, the actual
full-adele pullback comparison is a homeomorphism for the final topologies. -/
def NumberFieldFixedModelPullbackStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g), IsLimit c →
    letI : TopologicalSpace (NumberFieldFixedModelAdelePoints K S X) :=
      numberFieldFixedModelAdelePointTopology K S X
    letI : TopologicalSpace (NumberFieldFixedModelAdelePoints K S Y) :=
      numberFieldFixedModelAdelePointTopology K S Y
    @IsHomeomorph
      (NumberFieldFixedModelAdelePoints K S c.pt)
      {q : NumberFieldFixedModelAdelePoints K S X ×
        NumberFieldFixedModelAdelePoints K S Y // q.1 ≫ f = q.2 ≫ g}
      (numberFieldFixedModelAdelePointTopology K S c.pt) inferInstance
      (affineSchemePullbackPointComparison
        ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) c)

/-- The full-adele fixed-model pullback assertion in both arithmetic cases. -/
def AdelicFixedModelPullbackStatement : Prop :=
  CurvePlaceFixedModelPullbackStatement.{u} ∧ NumberFieldFixedModelPullbackStatement.{u}

end Langlands.Global
