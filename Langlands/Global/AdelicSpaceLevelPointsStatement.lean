import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.Global.AdelicLevelModelPoints
import Langlands.Global.GlobalPlaceTopologyFacts

/-!
# Adelic-level points of separated finite type algebraic spaces

Conrad's Proposition 5.2: for a separated algebraic space of finite type over the
`S`-integers of a global field, the points with values in the adelic level ring
are the families of local points, valued in the completions at places of `S` and
in the completed valuation rings away from `S`.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Finite type over an affine base `Spec C`: a surjective étale atlas by an actual
scheme that is locally of finite type and quasi-compact over `Spec C`. -/
def FiniteTypeOverRing (C : Type u) [CommRing C]
    (X : AlgebraicSpace (Spec (CommRingCat.of C))) : Prop :=
  HasAtlasProperty (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u}) X

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- Conrad's Proposition 5.2 for a number field: restriction to the local factors of
the full adelic level is bijective on points of a separated finite type space over
the `S`-integers. -/
def NumberFieldSpaceLevelPointsStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
      Function.Bijective
        (fun (p : RingPoints ((S : Set (FinitePlace K)).integer K) X
            (numberFieldAdeleLevel K S)) (i : NumberFieldLevelFactorIndex K S) =>
          RingPoints.changeRing (numberFieldLevelFactorAlgHom K S i) p)

/-- Conrad's Proposition 5.2 for a global function field and a nonempty finite set `S`
of places: restriction to the local factors of the curve-place adelic level is
bijective on points of a separated finite type space over the `S`-integers. -/
def CurvePlaceSpaceLevelPointsStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)), S.Nonempty →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))),
    IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      Function.Bijective
        (fun (p : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
            (i : CurvePlaceLevelFactorIndex k F S) =>
          RingPoints.changeRing (curvePlaceLevelFactorAlgHom k F S i) p)

/-- Conrad's Proposition 5.2 for global fields of both characteristics. -/
def AdelicSpaceLevelPointsStatement : Prop :=
  NumberFieldSpaceLevelPointsStatement.{u} ∧ CurvePlaceSpaceLevelPointsStatement.{u}

end Langlands.Global
