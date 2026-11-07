import Langlands.Global.AdelicGenericFiberPoints
import Langlands.AlgebraicGeometry.SchemeFiberGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.NumberTheory.FunctionField

/-! # Compatible smooth arithmetic models of a field morphism -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- An actual compatible arithmetic-model existence template for a specified
property of a function-field morphism. No claim for arbitrary properties is made. -/
def CurvePlaceSpreadMorphismPropertyExistenceStatement
    (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (Y W : Over (Spec (CommRingCat.of F)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (g : Y ⟶ W), P g.left →
    ∃ (T : AdelicLevelIndexAbove S)
      (M N : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T.val)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      LocallyOfFiniteType N.hom ∧ QuasiCompact N.hom ∧ IsSeparated N.hom ∧
      ∃ (e : curvePlaceModelGenericFiber k F T.val M ≅ Y)
        (f : curvePlaceModelGenericFiber k F T.val N ≅ W) (gm : M ⟶ N),
        P gm.left ∧
          (Over.pullback (Spec.map (CommRingCat.ofHom
            (curvePlaceSIntegers k F T.val).subtype))).map gm ≫ f.hom = e.hom ≫ g

/-- The corresponding template for the original number-field integer rings. -/
def NumberFieldSpreadMorphismPropertyExistenceStatement
    (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (Y W : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (g : Y ⟶ W), P g.left →
    ∃ (T : AdelicLevelIndexAbove S)
      (M N : Over (Spec (CommRingCat.of ((T.val : Set (FinitePlace K)).integer K)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      LocallyOfFiniteType N.hom ∧ QuasiCompact N.hom ∧ IsSeparated N.hom ∧
      ∃ (e : numberFieldModelGenericFiber K T.val M ≅ Y)
        (f : numberFieldModelGenericFiber K T.val N ≅ W) (gm : M ⟶ N),
        P gm.left ∧
          (Over.pullback (Spec.map (CommRingCat.ofHom
            ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype))).map gm ≫
            f.hom = e.hom ≫ g

/-- Compatible function-field models for smoothness alone, and for
smoothness together with a prescribed full fibre geometry. -/
def CurvePlaceSpreadSmoothExistenceStatement : Prop :=
  CurvePlaceSpreadMorphismPropertyExistenceStatement.{u} @Smooth ∧
    ∀ d : ℕ, CurvePlaceSpreadMorphismPropertyExistenceStatement.{u}
      (@Smooth ⊓ NonemptyGeometricallyConnectedPureDimensionFibers d)

/-- Compatible number-field models with the same two conclusions. -/
def NumberFieldSpreadSmoothExistenceStatement : Prop :=
  NumberFieldSpreadMorphismPropertyExistenceStatement.{u} @Smooth ∧
    ∀ d : ℕ, NumberFieldSpreadMorphismPropertyExistenceStatement.{u}
      (@Smooth ⊓ NonemptyGeometricallyConnectedPureDimensionFibers d)

/-- Actual compatible smooth arithmetic models in both characteristics. -/
def AdelicSpreadSmoothExistenceStatement : Prop :=
  CurvePlaceSpreadSmoothExistenceStatement.{u} ∧
    NumberFieldSpreadSmoothExistenceStatement.{u}

end Langlands.Global
