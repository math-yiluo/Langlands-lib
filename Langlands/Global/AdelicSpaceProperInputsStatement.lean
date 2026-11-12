import Langlands.Global.AdelicSpaceSpreadMapStatement

/-!
# Arithmetic model inputs for proper adelic maps of algebraic spaces

The proper-model replacement and finite-level steps in Conrad's proof of Proposition 4.4,
carried over to algebraic spaces on printed p.17 before Proposition 5.8.
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- At every level above a separated finite-type function-field model, a proper model
morphism induces a proper map, and its full-adele inverse image of the target stage is the
source stage. -/
def CurvePlaceSpaceProperStagesStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)), S.Nonempty →
    ∀ (X Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))),
      IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      IsSeparated Z → FiniteTypeOverRing (curvePlaceSIntegers k F S) Z →
      ∀ g : X ⟶ Z, IsProperMorphism g → ∀ T : AdelicLevelIndexAbove S,
        @IsProperMap
          (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
          (RingPoints (curvePlaceSIntegers k F S) Z (curvePlaceAdeleLevelOver k F S T))
          (curvePlaceSpaceStageTopology k F S X T)
          (curvePlaceSpaceStageTopology k F S Z T) (RingPoints.map g) ∧
        (RingPoints.map g : CurvePlaceSpaceAdelePoints k F S X →
            CurvePlaceSpaceAdelePoints k F S Z) ⁻¹'
              Set.range (curvePlaceSpaceStageMap k F S Z T) =
          Set.range (curvePlaceSpaceStageMap k F S X T)

/-- The proper-stage and exact-preimage assertions for number fields, including all
infinite places in every level. -/
def NumberFieldSpaceProperStagesStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Z : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
    IsSeparated Z → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Z →
    ∀ g : X ⟶ Z, IsProperMorphism g → ∀ T : AdelicLevelIndexAbove S,
      @IsProperMap
        (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
        (RingPoints ((S : Set (FinitePlace K)).integer K) Z (numberFieldAdeleLevelOver K S T))
        (numberFieldSpaceStageTopology K S X T)
        (numberFieldSpaceStageTopology K S Z T) (RingPoints.map g) ∧
      (RingPoints.map g : NumberFieldSpaceAdelePoints K S X →
          NumberFieldSpaceAdelePoints K S Z) ⁻¹'
            Set.range (numberFieldSpaceStageMap K S Z T) =
        Set.range (numberFieldSpaceStageMap K S X T)

/-- The finite-level properness and exact full-adele preimages in both characteristics. -/
def AdelicSpaceProperStagesStatement : Prop :=
  CurvePlaceSpaceProperStagesStatement.{u} ∧ NumberFieldSpaceProperStagesStatement.{u}

/-- A proper field morphism between the generic fibres of two supplied separated finite-type
function-field models admits a proper morphism between separated finite-type models over one
ring of `T`-integers, with the specified commuting generic-fibre square. -/
def CurvePlaceSpaceProperModelStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F)), S.Nonempty → U.Nonempty →
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      (Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F U)))),
      IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      IsSeparated Z → FiniteTypeOverRing (curvePlaceSIntegers k F U) Z →
      ∀ (Y W : AlgebraicSpace (Spec (CommRingCat.of F)))
        (_e : curvePlaceSpaceGenericFiber k F S X ≅ Y)
        (_f : curvePlaceSpaceGenericFiber k F U Z ≅ W) (g : Y ⟶ W),
        IsProperMorphism g →
          ∃ (T : Finset (AlgebraicCurve.Place k F))
            (M N : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F T)))),
            T.Nonempty ∧ IsSeparated M ∧ FiniteTypeOverRing (curvePlaceSIntegers k F T) M ∧
            IsSeparated N ∧ FiniteTypeOverRing (curvePlaceSIntegers k F T) N ∧
            ∃ (eT : curvePlaceSpaceGenericFiber k F T M ≅ Y)
              (fT : curvePlaceSpaceGenericFiber k F T N ≅ W) (gm : M ⟶ N),
              IsProperMorphism gm ∧
                baseChangeMap (Spec.map (CommRingCat.ofHom
                  (curvePlaceSIntegers k F T).subtype)) gm ≫ fT.hom = eT.hom ≫ g

/-- The proper-model replacement for number fields, with the specified commuting square. -/
def NumberFieldSpaceProperModelStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S U : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : AlgebraicSpace (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
    IsSeparated Z → FiniteTypeOverRing ((U : Set (FinitePlace K)).integer K) Z →
    ∀ (Y W : AlgebraicSpace (Spec (CommRingCat.of K)))
      (_e : numberFieldSpaceGenericFiber K S X ≅ Y)
      (_f : numberFieldSpaceGenericFiber K U Z ≅ W) (g : Y ⟶ W),
      IsProperMorphism g →
        ∃ (T : Finset (FinitePlace K))
          (M N : AlgebraicSpace (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K)))),
          IsSeparated M ∧ FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) M ∧
          IsSeparated N ∧ FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) N ∧
          ∃ (eT : numberFieldSpaceGenericFiber K T M ≅ Y)
            (fT : numberFieldSpaceGenericFiber K T N ≅ W) (gm : M ⟶ N),
            IsProperMorphism gm ∧
              baseChangeMap (Spec.map (CommRingCat.ofHom
                ((T : Set (FinitePlace K)).integer K).toSubring.subtype)) gm ≫ fT.hom =
                  eT.hom ≫ g

/-- Proper arithmetic model replacements in both characteristics. -/
def AdelicSpaceProperModelStatement : Prop :=
  CurvePlaceSpaceProperModelStatement.{u} ∧ NumberFieldSpaceProperModelStatement.{u}

/-- The arithmetic model inputs in the proof of Conrad's Proposition 5.8: properness on
stages with exact full-adele preimages, and a proper model of the field morphism. -/
def AdelicSpaceProperInputsStatement : Prop :=
  AdelicSpaceProperStagesStatement.{u} ∧ AdelicSpaceProperModelStatement.{u}

end Langlands.Global
