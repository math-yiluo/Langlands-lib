import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.NumberTheory.FunctionField

/-! # Eventual separatedness of supplied arithmetic spreads -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- A supplied finite-type function-field model has separated generic fiber
exactly when its actual base change to some finite superlevel is separated. -/
def CurvePlaceSpreadEventualSeparationStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (M : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom],
    IsSeparated (curvePlaceModelGenericFiber k F S M).hom ↔
      ∃ T : AdelicLevelIndexAbove S,
        IsSeparated (curvePlaceLevelModelBaseChange k F T.property M).hom

/-- The corresponding equivalence for a supplied finite-type number-field model,
using the original number field and literal inclusions of integer rings. -/
def NumberFieldSpreadEventualSeparationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (M : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom],
    IsSeparated (numberFieldModelGenericFiber K S M).hom ↔
      ∃ T : AdelicLevelIndexAbove S,
        IsSeparated (numberFieldLevelModelBaseChange K T.property M).hom

/-- Eventual separatedness for actual arithmetic models in both characteristics. -/
def AdelicSpreadEventualSeparationStatement : Prop :=
  CurvePlaceSpreadEventualSeparationStatement.{u} ∧
    NumberFieldSpreadEventualSeparationStatement.{u}

end Langlands.Global
