import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.NumberTheory.FunctionField

/-! # Existence of actual arithmetic spreads for finite-type field schemes -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- A finite-type function-field scheme descends to actual outside-`T`
integers for a finite set `T` containing any prescribed initial set. -/
def CurvePlaceSpreadExistenceStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (Y : Over (Spec (CommRingCat.of F)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom],
    ∃ (T : AdelicLevelIndexAbove S)
      (M : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T.val)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧
        Nonempty (curvePlaceModelGenericFiber k F T.val M ≅ Y)

/-- The corresponding existence of an actual integer-ring spread for an
arbitrary finite-type scheme over the original number field. -/
def NumberFieldSpreadExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (Y : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom],
    ∃ (T : AdelicLevelIndexAbove S)
      (M : Over (Spec (CommRingCat.of ((T.val : Set (FinitePlace K)).integer K)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧
        Nonempty (numberFieldModelGenericFiber K T.val M ≅ Y)

/-- Actual arithmetic spreads exist in both characteristics. -/
def AdelicSpreadExistenceStatement : Prop :=
  CurvePlaceSpreadExistenceStatement.{u} ∧
    NumberFieldSpreadExistenceStatement.{u}

end Langlands.Global
