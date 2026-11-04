import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.Compactness.Compact
import Mathlib.NumberTheory.FunctionField

/-! # Compactness of actual adelic points of proper field schemes -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- A proper function-field scheme has compact adelic points for the topology
from any supplied finite-type arithmetic spread. -/
def CurvePlaceSpreadCompactnessStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) [IsProper Y.hom],
    @CompactSpace (CurvePlaceAdelePoints k F Y)
      (curvePlaceSpreadAdelePointTopology k F S X Y e)

/-- Compactness on full number-field adeles, including all infinite factors. -/
def NumberFieldSpreadCompactnessStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) [IsProper Y.hom],
    @CompactSpace (NumberFieldAdelePoints K Y)
      (numberFieldSpreadAdelePointTopology K S X Y e)

/-- The compactness consequence of Conrad Proposition 4.4 in both characteristics. -/
def AdelicSpreadCompactnessStatement : Prop :=
  CurvePlaceSpreadCompactnessStatement.{u} ∧
    NumberFieldSpreadCompactnessStatement.{u}

end Langlands.Global
