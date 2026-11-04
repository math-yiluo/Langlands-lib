import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.NumberTheory.FunctionField

/-! # Proper arithmetic models of a proper field morphism -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- A proper map to a separated finite-type function-field scheme admits
separated finite-type actual integer models and a proper model morphism. -/
def CurvePlaceSpreadProperExistenceStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (Y W : Over (Spec (CommRingCat.of F)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (g : Y ⟶ W) [IsProper g.left],
    ∃ (T : AdelicLevelIndexAbove S)
      (M N : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T.val)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      LocallyOfFiniteType N.hom ∧ QuasiCompact N.hom ∧ IsSeparated N.hom ∧
      ∃ (e : curvePlaceModelGenericFiber k F T.val M ≅ Y)
        (f : curvePlaceModelGenericFiber k F T.val N ≅ W) (gm : M ⟶ N),
        IsProper gm.left ∧
          (Over.pullback (Spec.map (CommRingCat.ofHom
            (curvePlaceSIntegers k F T.val).subtype))).map gm ≫ f.hom = e.hom ≫ g

/-- The corresponding proper-model existence over the original number field,
after enlargement of any prescribed finite set of finite places. -/
def NumberFieldSpreadProperExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (Y W : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (g : Y ⟶ W) [IsProper g.left],
    ∃ (T : AdelicLevelIndexAbove S)
      (M N : Over (Spec (CommRingCat.of ((T.val : Set (FinitePlace K)).integer K)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      LocallyOfFiniteType N.hom ∧ QuasiCompact N.hom ∧ IsSeparated N.hom ∧
      ∃ (e : numberFieldModelGenericFiber K T.val M ≅ Y)
        (f : numberFieldModelGenericFiber K T.val N ≅ W) (gm : M ⟶ N),
        IsProper gm.left ∧
          (Over.pullback (Spec.map (CommRingCat.ofHom
            ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype))).map gm ≫
            f.hom = e.hom ≫ g

/-- Actual proper arithmetic model morphisms in both characteristics. -/
def AdelicSpreadProperExistenceStatement : Prop :=
  CurvePlaceSpreadProperExistenceStatement.{u} ∧
    NumberFieldSpreadProperExistenceStatement.{u}

end Langlands.Global
