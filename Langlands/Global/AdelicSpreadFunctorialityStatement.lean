import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Functoriality on actual adelic points of generic fibers -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Arbitrary field-scheme morphisms are continuous for independently chosen
finite-type function-field spreads. -/
def CurvePlaceSpreadFunctorialityStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F U Z ≅ W)
    (g : Y ⟶ W),
    Continuous[curvePlaceSpreadAdelePointTopology k F S X Y e,
      curvePlaceSpreadAdelePointTopology k F U Z W f]
      (fun p : CurvePlaceAdelePoints k F Y => (p ≫ g : CurvePlaceAdelePoints k F W))

/-- Arbitrary number-field scheme morphisms are continuous on full-adele points
for independently chosen finite-type spreads. -/
def NumberFieldSpreadFunctorialityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S U : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K U Z ≅ W)
    (g : Y ⟶ W),
    Continuous[numberFieldSpreadAdelePointTopology K S X Y e,
      numberFieldSpreadAdelePointTopology K U Z W f]
      (fun p : NumberFieldAdelePoints K Y => (p ≫ g : NumberFieldAdelePoints K W))

/-- Functoriality for actual adelic scheme points with arbitrary specified
finite-type arithmetic spreads. -/
def AdelicSpreadFunctorialityStatement : Prop :=
  CurvePlaceSpreadFunctorialityStatement.{u} ∧
    NumberFieldSpreadFunctorialityStatement.{u}

end Langlands.Global
