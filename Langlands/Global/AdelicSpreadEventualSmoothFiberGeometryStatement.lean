import Langlands.Global.AdelicGenericFiberPoints
import Langlands.AlgebraicGeometry.SchemeFiberGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.NumberTheory.FunctionField

/-! # Smooth fibre geometry after an actual arithmetic enlargement -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Detection of a specified relative property on supplied finite-type
function-field models, using the literal integer-subring inclusions. -/
def CurvePlaceSpreadEventualPropertyStatement
    (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y),
    P (((Over.pullback
      (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))).map f).left) ↔
      ∃ T : AdelicLevelIndexAbove S,
        P (((Over.pullback
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property)))).map
            f).left)

/-- The same relative-property assertion for supplied number-field models
and their original outside-set integer rings. -/
def NumberFieldSpreadEventualPropertyStatement
    (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y),
    P (((Over.pullback
      (Spec.map (CommRingCat.ofHom
        ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).map f).left) ↔
      ∃ T : AdelicLevelIndexAbove S,
        P (((Over.pullback
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))).map
            f).left)

/-- Eventual smoothness, eventual nonempty geometrically connected fibres of
pure dimension `d`, and their simultaneous realization at one function-field
integer level. The property templates alone assert no arbitrary descent law. -/
def CurvePlaceSpreadEventualSmoothFiberGeometryStatement : Prop :=
  CurvePlaceSpreadEventualPropertyStatement.{u} @Smooth ∧
    ∀ d : ℕ,
      CurvePlaceSpreadEventualPropertyStatement.{u}
        (NonemptyGeometricallyConnectedPureDimensionFibers d) ∧
      CurvePlaceSpreadEventualPropertyStatement.{u}
        (@Smooth ⊓ NonemptyGeometricallyConnectedPureDimensionFibers d)

/-- All three equivalences over every actual number field. -/
def NumberFieldSpreadEventualSmoothFiberGeometryStatement : Prop :=
  NumberFieldSpreadEventualPropertyStatement.{u} @Smooth ∧
    ∀ d : ℕ,
      NumberFieldSpreadEventualPropertyStatement.{u}
        (NonemptyGeometricallyConnectedPureDimensionFibers d) ∧
      NumberFieldSpreadEventualPropertyStatement.{u}
        (@Smooth ⊓ NonemptyGeometricallyConnectedPureDimensionFibers d)

/-- Both arithmetic branches, with a common enlarged level for the combined
smoothness and geometric fibre condition, and no affineness or separatedness. -/
def AdelicSpreadEventualSmoothFiberGeometryStatement : Prop :=
  CurvePlaceSpreadEventualSmoothFiberGeometryStatement.{u} ∧
    NumberFieldSpreadEventualSmoothFiberGeometryStatement.{u}

end Langlands.Global
