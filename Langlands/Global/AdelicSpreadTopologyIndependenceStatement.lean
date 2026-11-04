import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Independence of the adelic topology from a specified arithmetic spread -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Any two finite-type function-field spreads induce the same actual point topology. -/
def CurvePlaceSpreadTopologyIndependenceStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F U Z ≅ Y),
    curvePlaceSpreadAdelePointTopology k F S X Y e =
      curvePlaceSpreadAdelePointTopology k F U Z Y f

/-- Any two finite-type number-field spreads induce the same full-adele point topology. -/
def NumberFieldSpreadTopologyIndependenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S U : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K U Z ≅ Y),
    numberFieldSpreadAdelePointTopology K S X Y e =
      numberFieldSpreadAdelePointTopology K U Z Y f

/-- Equality of the actual adelic topologies from arbitrary finite-type spreads. -/
def AdelicSpreadTopologyIndependenceStatement : Prop :=
  CurvePlaceSpreadTopologyIndependenceStatement.{u} ∧
    NumberFieldSpreadTopologyIndependenceStatement.{u}

end Langlands.Global
