import Langlands.Global.AdelicSpacePointTopology
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismProperties
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper and smooth maps of algebraic spaces on adelic points

Conrad's Proposition 5.8: a proper map between separated algebraic spaces of finite type over
a global field induces a topologically proper map on adelic points. Conrad's Theorem 5.9: a
smooth surjective map between separated algebraic spaces of finite type over a global field,
with geometrically connected fibres, induces an open map on adelic points. The adelic points
of a space over the field carry the topology attached to a separated model of finite type over
a ring of `S`-integers; the statements hold for arbitrary models of source and target.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

section Curve

/-- Function fields, Conrad's Proposition 5.8: a proper map `g : Y ⟶ W` of algebraic spaces
over `F` induces a proper map on adelic points, for arbitrary separated models of finite type
of `Y` and `W`. -/
def CurvePlaceSpaceSpreadProperMapStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F)), S.Nonempty → U.Nonempty →
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      (Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F U)))),
      IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      IsSeparated Z → FiniteTypeOverRing (curvePlaceSIntegers k F U) Z →
      ∀ (Y W : AlgebraicSpace (Spec (CommRingCat.of F)))
        (e : curvePlaceSpaceGenericFiber k F S X ≅ Y)
        (f : curvePlaceSpaceGenericFiber k F U Z ≅ W) (g : Y ⟶ W),
        IsProperMorphism g →
          @IsProperMap (CurvePlaceSpaceFieldAdelePoints k F Y)
            (CurvePlaceSpaceFieldAdelePoints k F W)
            (curvePlaceSpaceSpreadTopology k F S X Y e)
            (curvePlaceSpaceSpreadTopology k F U Z W f) (RingPoints.map g)

/-- Function fields, Conrad's Theorem 5.9: a smooth surjective map `g : Y ⟶ W` of algebraic
spaces over `F` with geometrically connected fibres induces an open map on adelic points, for
arbitrary separated models of finite type of `Y` and `W`. -/
def CurvePlaceSpaceSpreadSmoothOpenStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F)), S.Nonempty → U.Nonempty →
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      (Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F U)))),
      IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      IsSeparated Z → FiniteTypeOverRing (curvePlaceSIntegers k F U) Z →
      ∀ (Y W : AlgebraicSpace (Spec (CommRingCat.of F)))
        (e : curvePlaceSpaceGenericFiber k F S X ≅ Y)
        (f : curvePlaceSpaceGenericFiber k F U Z ≅ W) (g : Y ⟶ W),
        IsSmoothMorphism g → IsSurjectiveMorphism g → HasGeometricallyConnectedFibres g →
          @IsOpenMap (CurvePlaceSpaceFieldAdelePoints k F Y)
            (CurvePlaceSpaceFieldAdelePoints k F W)
            (curvePlaceSpaceSpreadTopology k F S X Y e)
            (curvePlaceSpaceSpreadTopology k F U Z W f) (RingPoints.map g)

end Curve

section NumberField

/-- Number fields, Conrad's Proposition 5.8: a proper map `g : Y ⟶ W` of algebraic spaces over
`K` induces a proper map on adelic points, for arbitrary separated models of finite type of
`Y` and `W`. -/
def NumberFieldSpaceSpreadProperMapStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S U : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : AlgebraicSpace (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
    IsSeparated Z → FiniteTypeOverRing ((U : Set (FinitePlace K)).integer K) Z →
    ∀ (Y W : AlgebraicSpace (Spec (CommRingCat.of K)))
      (e : numberFieldSpaceGenericFiber K S X ≅ Y)
      (f : numberFieldSpaceGenericFiber K U Z ≅ W) (g : Y ⟶ W),
      IsProperMorphism g →
        @IsProperMap (NumberFieldSpaceFieldAdelePoints K Y) (NumberFieldSpaceFieldAdelePoints K W)
          (numberFieldSpaceSpreadTopology K S X Y e)
          (numberFieldSpaceSpreadTopology K U Z W f) (RingPoints.map g)

/-- Number fields, Conrad's Theorem 5.9: a smooth surjective map `g : Y ⟶ W` of algebraic
spaces over `K` with geometrically connected fibres induces an open map on adelic points, for
arbitrary separated models of finite type of `Y` and `W`. -/
def NumberFieldSpaceSpreadSmoothOpenStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S U : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : AlgebraicSpace (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
    IsSeparated Z → FiniteTypeOverRing ((U : Set (FinitePlace K)).integer K) Z →
    ∀ (Y W : AlgebraicSpace (Spec (CommRingCat.of K)))
      (e : numberFieldSpaceGenericFiber K S X ≅ Y)
      (f : numberFieldSpaceGenericFiber K U Z ≅ W) (g : Y ⟶ W),
      IsSmoothMorphism g → IsSurjectiveMorphism g → HasGeometricallyConnectedFibres g →
        @IsOpenMap (NumberFieldSpaceFieldAdelePoints K Y) (NumberFieldSpaceFieldAdelePoints K W)
          (numberFieldSpaceSpreadTopology K S X Y e)
          (numberFieldSpaceSpreadTopology K U Z W f) (RingPoints.map g)

end NumberField

/-- Conrad's Proposition 5.8 for global fields of both characteristics. -/
def AdelicSpaceSpreadProperMapStatement : Prop :=
  CurvePlaceSpaceSpreadProperMapStatement.{u} ∧ NumberFieldSpaceSpreadProperMapStatement.{u}

/-- Conrad's Theorem 5.9 for global fields of both characteristics. -/
def AdelicSpaceSpreadSmoothOpenStatement : Prop :=
  CurvePlaceSpaceSpreadSmoothOpenStatement.{u} ∧ NumberFieldSpaceSpreadSmoothOpenStatement.{u}

end Langlands.Global
