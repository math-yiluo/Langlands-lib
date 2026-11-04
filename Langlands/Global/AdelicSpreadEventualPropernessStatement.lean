import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.NumberTheory.FunctionField

/-! # Eventual properness of supplied arithmetic model morphisms -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- A morphism of supplied finite-type function-field models has proper generic
fiber exactly when its actual base change to some finite superlevel is proper. -/
def CurvePlaceSpreadEventualPropernessStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y),
    IsProper (((Over.pullback
      (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))).map f).left) ↔
      ∃ T : AdelicLevelIndexAbove S,
        IsProper (((Over.pullback
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property)))).map
            f).left)

/-- The corresponding properness equivalence over the original number field
and the literal inclusions of its outside-set integer rings. -/
def NumberFieldSpreadEventualPropernessStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y),
    IsProper (((Over.pullback
      (Spec.map (CommRingCat.ofHom
        ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).map f).left) ↔
      ∃ T : AdelicLevelIndexAbove S,
        IsProper (((Over.pullback
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))).map
            f).left)

/-- Eventual properness for supplied actual arithmetic model morphisms in both
characteristics, including empty initial levels and nonaffine models. -/
def AdelicSpreadEventualPropernessStatement : Prop :=
  CurvePlaceSpreadEventualPropernessStatement.{u} ∧
    NumberFieldSpreadEventualPropernessStatement.{u}

end Langlands.Global
