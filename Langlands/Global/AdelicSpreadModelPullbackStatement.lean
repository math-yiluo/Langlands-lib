import Langlands.Global.AdelicGenericFiberPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbackPoints
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Generic-fiber adelic points of specified arithmetic pullback cones -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Pulling a separated-base function-field model cone to the field preserves its
actual adelic pullback comparison for the topologies from those models. -/
def CurvePlaceSpreadModelPullbackStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g), IsLimit c →
    let G := Over.pullback
      (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
    letI : TopologicalSpace (CurvePlaceAdelePoints k F (G.obj X)) :=
      curvePlaceSpreadAdelePointTopology k F S X (G.obj X) (Iso.refl _)
    letI : TopologicalSpace (CurvePlaceAdelePoints k F (G.obj Y)) :=
      curvePlaceSpreadAdelePointTopology k F S Y (G.obj Y) (Iso.refl _)
    @IsHomeomorph
      (CurvePlaceAdelePoints k F (G.obj c.pt))
      {q : CurvePlaceAdelePoints k F (G.obj X) ×
        CurvePlaceAdelePoints k F (G.obj Y) // q.1 ≫ G.map f = q.2 ≫ G.map g}
      (curvePlaceSpreadAdelePointTopology k F S c.pt (G.obj c.pt) (Iso.refl _))
      inferInstance
      (affineSchemePullbackPointComparison F (CurvePlaceAdeleRing k F) (c.map G))

/-- The full-number-field analogue, with every infinite factor retained. -/
def NumberFieldSpreadModelPullbackStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g), IsLimit c →
    let G := Over.pullback
      (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
    letI : TopologicalSpace (NumberFieldAdelePoints K (G.obj X)) :=
      numberFieldSpreadAdelePointTopology K S X (G.obj X) (Iso.refl _)
    letI : TopologicalSpace (NumberFieldAdelePoints K (G.obj Y)) :=
      numberFieldSpreadAdelePointTopology K S Y (G.obj Y) (Iso.refl _)
    @IsHomeomorph
      (NumberFieldAdelePoints K (G.obj c.pt))
      {q : NumberFieldAdelePoints K (G.obj X) ×
        NumberFieldAdelePoints K (G.obj Y) // q.1 ≫ G.map f = q.2 ≫ G.map g}
      (numberFieldSpreadAdelePointTopology K S c.pt (G.obj c.pt) (Iso.refl _))
      inferInstance
      (affineSchemePullbackPointComparison K (Adeles K) (c.map G))

/-- Both arithmetic generic-fiber comparisons for specified model pullbacks. -/
def AdelicSpreadModelPullbackStatement : Prop :=
  CurvePlaceSpreadModelPullbackStatement.{u} ∧ NumberFieldSpreadModelPullbackStatement.{u}

end Langlands.Global
