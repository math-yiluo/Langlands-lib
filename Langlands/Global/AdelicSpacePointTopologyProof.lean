import Langlands.Global.AdelicSpaceFibreProductProof
import Langlands.Global.AdelicSpacePointSchemeProof
import Langlands.Global.AdelicFixedModelAlgebraColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointStatement

/-!
# Conrad's p.17 claims on adelic points of separated algebraic spaces

This module assembles the clauses of `Langlands.Global.AdelicSpacePointTopologyStatement` for
which the topological arguments are given in this development: the covering by levels,
local compactness, the Hausdorff property and second countability, functoriality, closed
immersions, fibre products and the scheme case. The covering by levels is the filtered colimit
comparison for points of finitely presented algebraic spaces
(`SpaceFilteredRingPointComparison`), applied to the adeles as the colimit of the levels.
Separated spaces of finite type over the Noetherian `S`-integers are locally of finite
presentation.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

namespace AdelicSpacePointTopologyProof

open AdelicSpacePointMapsProof AdelicSpacePointStagesProof AdelicSpacePointsProof
  AdelicSpaceFibreProductProof AdelicSpacePointSchemeProof

/-- Over a Noetherian ring, finite type spaces are locally of finite presentation. -/
theorem locallyOfFinitePresentationOverBase {C : Type u} [CommRing C] [IsNoetherianRing C]
    {X : AlgebraicSpace (Spec (CommRingCat.of C))} (hft : FiniteTypeOverRing C X) :
    LocallyOfFinitePresentationOverBase X := by
  obtain ⟨U, a, ha, hs, hP⟩ := hft
  have : LocallyOfFiniteType U.hom := hP.1
  exact ⟨U, a, ha, hs, LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr this⟩

variable (hL1 : SpaceFilteredRingPointComparison.{u})
include hL1

/-- **Every adelic point comes from a level**, number fields. -/
theorem numberField_cover (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    {X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (x : NumberFieldSpaceAdelePoints K S X) :
    ∃ (T : AdelicLevelIndexAbove S)
      (y : RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)),
      numberFieldSpaceStageMap K S X T y = x := by
  have : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  exact (hL1 _ (AdelicLevelIndexAbove S) (numberFieldAdeleLevelOverDiagram K S)
    (numberFieldAdeleOverCocone K S) (numberFieldAdeleOverIsColimit K S) X).2
      (locallyOfFinitePresentationOverBase hft) x

/-- **Every adelic point comes from a level**, global function fields. -/
theorem curve_cover (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    {X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (x : CurvePlaceSpaceAdelePoints k F S X) :
    ∃ (T : AdelicLevelIndexAbove S)
      (y : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)),
      curvePlaceSpaceStageMap k F S X T y = x := by
  have : IsNoetherianRing (curvePlaceSIntegers k F S) := (adelicSIntegersNoetherian.1 k F S).1
  exact (hL1 _ (AdelicLevelIndexAbove S) (curvePlaceAdeleLevelOverDiagram k F S)
    (curvePlaceAdeleOverCocone k F S) (curvePlaceAdeleOverIsColimit k F S) X).2
      (locallyOfFinitePresentationOverBase hft) x

/-- **Conrad's p.17 claims on adelic points, number fields.** -/
theorem numberFieldSpaceAdelePoints : NumberFieldSpaceAdelePointsStatement.{u} := by
  intro K _ _ S X hX hft
  exact ⟨numberField_cover hL1 K S hft, numberField_stage_isOpenEmbedding K S hX hft,
    numberField_points_of_cover K S hX hft (numberField_cover hL1 K S hft)⟩

/-- **Conrad's p.17 claims on adelic points, global function fields.** -/
theorem curvePlaceSpaceAdelePoints : CurvePlaceSpaceAdelePointsStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S hS X hX hft
  exact ⟨curve_cover hL1 k F S hft, curve_stage_isOpenEmbedding k F S hX hS hft,
    curve_points_of_cover k F S hS hX hft (curve_cover hL1 k F S hft)⟩

/-- **Conrad's p.17 claims on morphisms, number fields.** -/
theorem numberFieldSpaceAdelePointMaps : NumberFieldSpaceAdelePointMapsStatement.{u} := by
  intro K _ _ S
  refine ⟨fun X Y f hX hftX hY hftY => ⟨numberField_continuous K S hY hftY f,
    numberField_closed K S hX hftX hY hftY f⟩, ?_⟩
  intro P X Y Z p₁ p₂ f g h hP hftP hX hftX hY hftY hZ hftZ
  exact numberField_fibreProduct K S p₁ p₂ f g (CoordinateFibreProduct.isPullback_hom h) hP hftP hX hftX hY hftY hZ hftZ
    (numberField_cover hL1 K S hftP)

/-- **Conrad's p.17 claims on morphisms, global function fields.** -/
theorem curvePlaceSpaceAdelePointMaps : CurvePlaceSpaceAdelePointMapsStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S hS
  refine ⟨fun X Y f hX hftX hY hftY => ⟨curve_continuous k F S hY hftY f,
    curve_closed k F S hS hX hftX hY hftY f⟩, ?_⟩
  intro P X Y Z p₁ p₂ f g h hP hftP hX hftX hY hftY hZ hftZ
  exact curve_fibreProduct k F S p₁ p₂ f g hS (CoordinateFibreProduct.isPullback_hom h) hP hftP hX hftX hY hftY hZ hftZ
    (curve_cover hL1 k F S hftP)

omit hL1 in
/-- **Conrad's p.17 claims on adelic points of separated algebraic spaces**, from the filtered
colimit comparison and the spread clauses. -/
theorem adelicSpacePointTopology_of_spread (hL1 : SpaceFilteredRingPointComparison.{u})
    (hC : CurvePlaceSpaceSpreadStatement.{u}) (hN : NumberFieldSpaceSpreadStatement.{u}) :
    AdelicSpacePointTopologyStatement.{u} :=
  ⟨⟨curvePlaceSpaceAdelePoints hL1, curvePlaceSpaceAdelePointMaps hL1,
      curvePlaceSpaceAdelePointScheme, hC⟩,
    ⟨numberFieldSpaceAdelePoints hL1, numberFieldSpaceAdelePointMaps hL1,
      numberFieldSpaceAdelePointScheme, hN⟩⟩

end AdelicSpacePointTopologyProof

end Langlands.Global
