import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Topological properties of actual adelic points from a specified spread -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Local compactness, second countability and separated-model Hausdorffness
of actual function-field adelic points with a specified arithmetic spread. -/
def CurvePlaceSpreadTopologicalPropertiesStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y),
    letI := curvePlaceSpreadAdelePointTopology k F S X Y e
    LocallyCompactSpace (CurvePlaceAdelePoints k F Y) ∧
      SecondCountableTopology (CurvePlaceAdelePoints k F Y) ∧
      (∀ [IsSeparated X.hom], T2Space (CurvePlaceAdelePoints k F Y))

/-- The full number-field point space retains every infinite completion. -/
def NumberFieldSpreadTopologicalPropertiesStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y),
    letI := numberFieldSpreadAdelePointTopology K S X Y e
    LocallyCompactSpace (NumberFieldAdelePoints K Y) ∧
      SecondCountableTopology (NumberFieldAdelePoints K Y) ∧
      (∀ [IsSeparated X.hom], T2Space (NumberFieldAdelePoints K Y))

/-- Actual adelic points of specified finite-type arithmetic spreads are
locally compact and second countable, and Hausdorff for separated spreads. -/
def AdelicSpreadTopologicalPropertiesStatement : Prop :=
  CurvePlaceSpreadTopologicalPropertiesStatement.{u} ∧
    NumberFieldSpreadTopologicalPropertiesStatement.{u}

end Langlands.Global
