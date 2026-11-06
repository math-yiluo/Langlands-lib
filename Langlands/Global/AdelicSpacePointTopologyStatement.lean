import Langlands.Global.AdelicSpacePointTopology
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Topological properties of adelic points of algebraic spaces

Conrad, printed p.17: for a separated algebraic space of finite type over the `S`-integers of
a global field, every adelic point comes from a level, the levels are open, and the adelic
points form a locally compact Hausdorff space with a countable base. The topology is
functorial, carries closed immersions to closed embeddings, is compatible with fibre
products and recovers the scheme case. Separated algebraic spaces of finite type over the
global field have models, and the topology does not depend on the model.
-/

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

section Curve

/-- Function fields, fixed model: every adelic point comes from a level, each level is an open
embedding, and the adelic points are locally compact, Hausdorff and second countable. -/
def CurvePlaceSpaceAdelePointsStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)), S.Nonempty →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))),
    IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      (∀ x : CurvePlaceSpaceAdelePoints k F S X,
        ∃ (T : AdelicLevelIndexAbove S)
          (y : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)),
          curvePlaceSpaceStageMap k F S X T y = x) ∧
      (∀ T : AdelicLevelIndexAbove S,
        @IsOpenEmbedding _ _ (curvePlaceSpaceStageTopology k F S X T)
          (curvePlaceSpaceAdelePointTopology k F S X) (curvePlaceSpaceStageMap k F S X T)) ∧
      (@LocallyCompactSpace _ (curvePlaceSpaceAdelePointTopology k F S X) ∧
        @T2Space _ (curvePlaceSpaceAdelePointTopology k F S X) ∧
        @SecondCountableTopology _ (curvePlaceSpaceAdelePointTopology k F S X))

/-- Function fields, fixed model: maps of separated spaces of finite type induce continuous
maps on adelic points, closed immersions induce closed embeddings, and fibre products of
adelic points are compatible with fibre products of spaces. -/
def CurvePlaceSpaceAdelePointMapsStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)), S.Nonempty →
    (∀ (X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) (f : X ⟶ Y),
      IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      IsSeparated Y → FiniteTypeOverRing (curvePlaceSIntegers k F S) Y →
        @Continuous _ _ (curvePlaceSpaceAdelePointTopology k F S X)
          (curvePlaceSpaceAdelePointTopology k F S Y) (RingPoints.map f) ∧
        (IsClosedImmersion (hom f) →
          @IsClosedEmbedding _ _ (curvePlaceSpaceAdelePointTopology k F S X)
            (curvePlaceSpaceAdelePointTopology k F S Y) (RingPoints.map f))) ∧
    (∀ (P X Y Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z), IsPullback p₁ p₂ f g →
      IsSeparated P → FiniteTypeOverRing (curvePlaceSIntegers k F S) P →
      IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      IsSeparated Y → FiniteTypeOverRing (curvePlaceSIntegers k F S) Y →
      IsSeparated Z → FiniteTypeOverRing (curvePlaceSIntegers k F S) Z →
        letI := curvePlaceSpaceAdelePointTopology k F S X
        letI := curvePlaceSpaceAdelePointTopology k F S Y
        @IsEmbedding _ (CurvePlaceSpaceAdelePoints k F S X × CurvePlaceSpaceAdelePoints k F S Y)
          (curvePlaceSpaceAdelePointTopology k F S P) _
          (fun p => (RingPoints.map p₁ p, RingPoints.map p₂ p)))

/-- Function fields: for a separated scheme of finite type over the `S`-integers, the topology
on the adelic points of the associated algebraic space is the published scheme topology. -/
def CurvePlaceSpaceAdelePointSchemeStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)), S.Nonempty →
    ∀ (U : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [_root_.AlgebraicGeometry.IsSeparated U.hom],
      @IsHomeomorph _ _
        (curvePlaceSpaceAdelePointTopology k F S ((schemeToSpace _).obj U))
        (curvePlaceFixedModelAdelePointTopology k F S U)
        (schemeRingPointsEquiv (curvePlaceSIntegers k F S) U (curvePlaceAdeleOver k F S))

/-- Function fields: every separated algebraic space of finite type over `F` has a separated
model of finite type over the `S`-integers for some nonempty `S`, and the topology on its
adelic points does not depend on the model. -/
def CurvePlaceSpaceSpreadStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
    (∀ Y : AlgebraicSpace (Spec (CommRingCat.of F)), IsSeparated Y → FiniteTypeOverRing F Y →
      ∃ (S : Finset (AlgebraicCurve.Place k F)) (X :
        AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))),
        S.Nonempty ∧ IsSeparated X ∧ FiniteTypeOverRing (curvePlaceSIntegers k F S) X ∧
          Nonempty (curvePlaceSpaceGenericFiber k F S X ≅ Y)) ∧
    (∀ (S U : Finset (AlgebraicCurve.Place k F)), S.Nonempty → U.Nonempty →
      ∀ (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
        (Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F U)))),
        IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
        IsSeparated Z → FiniteTypeOverRing (curvePlaceSIntegers k F U) Z →
        ∀ (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
          (e : curvePlaceSpaceGenericFiber k F S X ≅ Y)
          (f : curvePlaceSpaceGenericFiber k F U Z ≅ Y),
          curvePlaceSpaceSpreadTopology k F S X Y e = curvePlaceSpaceSpreadTopology k F U Z Y f)

end Curve

section NumberField

/-- Number fields, fixed model: every adelic point comes from a level, each level is an open
embedding, and the adelic points are locally compact, Hausdorff and second countable. -/
def NumberFieldSpaceAdelePointsStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
      (∀ x : NumberFieldSpaceAdelePoints K S X,
        ∃ (T : AdelicLevelIndexAbove S)
          (y : RingPoints ((S : Set (FinitePlace K)).integer K) X
            (numberFieldAdeleLevelOver K S T)),
          numberFieldSpaceStageMap K S X T y = x) ∧
      (∀ T : AdelicLevelIndexAbove S,
        @IsOpenEmbedding _ _ (numberFieldSpaceStageTopology K S X T)
          (numberFieldSpaceAdelePointTopology K S X) (numberFieldSpaceStageMap K S X T)) ∧
      (@LocallyCompactSpace _ (numberFieldSpaceAdelePointTopology K S X) ∧
        @T2Space _ (numberFieldSpaceAdelePointTopology K S X) ∧
        @SecondCountableTopology _ (numberFieldSpaceAdelePointTopology K S X))

/-- Number fields, fixed model: maps of separated spaces of finite type induce continuous
maps on adelic points, closed immersions induce closed embeddings, and fibre products of
adelic points are compatible with fibre products of spaces. -/
def NumberFieldSpaceAdelePointMapsStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    (∀ (X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
      (f : X ⟶ Y),
      IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
      IsSeparated Y → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y →
        @Continuous _ _ (numberFieldSpaceAdelePointTopology K S X)
          (numberFieldSpaceAdelePointTopology K S Y) (RingPoints.map f) ∧
        (IsClosedImmersion (hom f) →
          @IsClosedEmbedding _ _ (numberFieldSpaceAdelePointTopology K S X)
            (numberFieldSpaceAdelePointTopology K S Y) (RingPoints.map f))) ∧
    (∀ (P X Y Z : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
      (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z), IsPullback p₁ p₂ f g →
      IsSeparated P → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) P →
      IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
      IsSeparated Y → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y →
      IsSeparated Z → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Z →
        letI := numberFieldSpaceAdelePointTopology K S X
        letI := numberFieldSpaceAdelePointTopology K S Y
        @IsEmbedding _ (NumberFieldSpaceAdelePoints K S X × NumberFieldSpaceAdelePoints K S Y)
          (numberFieldSpaceAdelePointTopology K S P) _
          (fun p => (RingPoints.map p₁ p, RingPoints.map p₂ p)))

/-- Number fields: for a separated scheme of finite type over the `S`-integers, the topology on
the adelic points of the associated algebraic space is the published scheme topology. -/
def NumberFieldSpaceAdelePointSchemeStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (U : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [_root_.AlgebraicGeometry.IsSeparated U.hom],
    @IsHomeomorph _ _
      (numberFieldSpaceAdelePointTopology K S ((schemeToSpace _).obj U))
      (numberFieldFixedModelAdelePointTopology K S U)
      (schemeRingPointsEquiv ((S : Set (FinitePlace K)).integer K) U (numberFieldAdeleOver K S))

/-- Number fields: every separated algebraic space of finite type over `K` has a separated
model of finite type over the `S`-integers for some `S`, and the topology on its adelic points
does not depend on the model. -/
def NumberFieldSpaceSpreadStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    (∀ Y : AlgebraicSpace (Spec (CommRingCat.of K)), IsSeparated Y → FiniteTypeOverRing K Y →
      ∃ (S : Finset (FinitePlace K)) (X :
        AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
        IsSeparated X ∧ FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X ∧
          Nonempty (numberFieldSpaceGenericFiber K S X ≅ Y)) ∧
    (∀ (S U : Finset (FinitePlace K))
      (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
      (Z : AlgebraicSpace (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K)))),
      IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
      IsSeparated Z → FiniteTypeOverRing ((U : Set (FinitePlace K)).integer K) Z →
      ∀ (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
        (e : numberFieldSpaceGenericFiber K S X ≅ Y)
        (f : numberFieldSpaceGenericFiber K U Z ≅ Y),
        numberFieldSpaceSpreadTopology K S X Y e = numberFieldSpaceSpreadTopology K U Z Y f)

end NumberField

/-- Conrad's p.17 claims on adelic points of separated algebraic spaces of finite type, for
global fields of both characteristics. -/
def AdelicSpacePointTopologyStatement : Prop :=
  (CurvePlaceSpaceAdelePointsStatement.{u} ∧ CurvePlaceSpaceAdelePointMapsStatement.{u} ∧
      CurvePlaceSpaceAdelePointSchemeStatement.{u} ∧ CurvePlaceSpaceSpreadStatement.{u}) ∧
    (NumberFieldSpaceAdelePointsStatement.{u} ∧ NumberFieldSpaceAdelePointMapsStatement.{u} ∧
      NumberFieldSpaceAdelePointSchemeStatement.{u} ∧ NumberFieldSpaceSpreadStatement.{u})

end Langlands.Global
