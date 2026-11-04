import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.NumberTheory.FunctionField

/-! # Existence of separated arithmetic spreads -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- A separated finite-type function-field scheme has a separated actual
integer-ring model after enlarging any prescribed finite place set. -/
def CurvePlaceSpreadSeparatedExistenceStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (Y : Over (Spec (CommRingCat.of F)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom],
    ∃ (T : AdelicLevelIndexAbove S)
      (M : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T.val)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
        Nonempty (curvePlaceModelGenericFiber k F T.val M ≅ Y)

/-- A separated finite-type number-field scheme has a separated actual
integer-ring model after enlarging any prescribed finite place set. -/
def NumberFieldSpreadSeparatedExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (Y : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom],
    ∃ (T : AdelicLevelIndexAbove S)
      (M : Over (Spec (CommRingCat.of ((T.val : Set (FinitePlace K)).integer K)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
        Nonempty (numberFieldModelGenericFiber K T.val M ≅ Y)

/-- Existence of separated actual arithmetic spreads in both characteristics. -/
def AdelicSpreadSeparatedExistenceStatement : Prop :=
  CurvePlaceSpreadSeparatedExistenceStatement.{u} ∧
    NumberFieldSpreadSeparatedExistenceStatement.{u}

end Langlands.Global
