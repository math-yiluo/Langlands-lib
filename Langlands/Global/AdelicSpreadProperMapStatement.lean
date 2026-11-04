import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.NumberTheory.FunctionField

/-! # Proper maps on actual generic-fiber adelic points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Proper field morphisms with separated target induce proper maps for
arbitrary specified finite-type function-field spreads. -/
def CurvePlaceSpreadProperMapStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F U Z ≅ W)
    [IsSeparated W.hom]
    (g : Y ⟶ W) [IsProper g.left],
    @IsProperMap (CurvePlaceAdelePoints k F Y) (CurvePlaceAdelePoints k F W)
      (curvePlaceSpreadAdelePointTopology k F S X Y e)
      (curvePlaceSpreadAdelePointTopology k F U Z W f)
      (fun p => p ≫ g)

/-- Proper field morphisms with separated target induce proper maps on actual
full-adele points for arbitrary specified finite-type number-field spreads. -/
def NumberFieldSpreadProperMapStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S U : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K U Z ≅ W)
    [IsSeparated W.hom]
    (g : Y ⟶ W) [IsProper g.left],
    @IsProperMap (NumberFieldAdelePoints K Y) (NumberFieldAdelePoints K W)
      (numberFieldSpreadAdelePointTopology K S X Y e)
      (numberFieldSpreadAdelePointTopology K U Z W f)
      (fun p => p ≫ g)

/-- Properness in both arithmetic cases for independently specified spreads. -/
def AdelicSpreadProperMapStatement : Prop :=
  CurvePlaceSpreadProperMapStatement.{u} ∧
    NumberFieldSpreadProperMapStatement.{u}

end Langlands.Global
