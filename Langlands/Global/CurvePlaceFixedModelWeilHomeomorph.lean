import Langlands.Global.CurvePlaceFixedLevelWeilEvaluation
import Langlands.Global.AdelicWeilLevelCofinality
import Langlands.Global.AdelicFixedModelPointComparisonProof
import Langlands.AlgebraicGeometry.PointTopology.FinalCoconeHomeomorph
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionFiniteType
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers

namespace Langlands.Global.CurvePlaceFixedModelWeilHomeomorph

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open CurvePlacePrincipalSIntegerFixedLevelRegroup AdelicWeilLevelCofinality

set_option backward.isDefEq.respectTransparency false

section Colimit

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (S : Finset (Place k F))
  (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
  [LocallyOfFinitePresentation X.hom]

/-- The original full-adele point cocone is an actual Type-valued colimit. -/
def pointCoconeIsColimit :
    IsColimit (ringPointCocone (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevelOverDiagram k F S) X (curvePlaceAdeleOverCocone k F S)) := by
  apply Nonempty.some
  apply (Types.isColimit_iff_coconeTypesIsColimit _).mpr
  exact ⟨((curvePlaceFixedModelPointComparisonProperties k F S X).2 inferInstance).2.1⟩

end Colimit

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  (Y : Over (Spec (CommRingCat.of
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))))))
  [LocallyOfFiniteType Y.hom] [CompactSpace Y.left]

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Every original upper transition is continuous, using the induced function-field presentation. -/
theorem upperTransition_continuous
    {U V : AdelicLevelIndexAbove (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))}
    (f : U ⟶ V) :
    Continuous[
      curvePlaceFixedModelStageTopology k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y U,
      curvePlaceFixedModelStageTopology k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y V]
      ((curvePlaceFixedModelPointDiagram k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y).map f) := by
  let : Algebra (RatFunc k) L :=
    ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
  let : IsScalarTower (RatFunc k) K L := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k (RatFunc k) L := .of_algebraMap_eq fun a => by
    change algebraMap k L a =
      algebraMap K L (algebraMap (RatFunc k) K (algebraMap k (RatFunc k) a))
    rw [← IsScalarTower.algebraMap_apply k (RatFunc k) K,
      ← IsScalarTower.algebraMap_apply k K L]
  let : FunctionField k L := Module.Finite.trans (R := RatFunc k) K L
  exact (curvePlaceFixedModelTransitionTopology k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
    Y U V (leOfHom f)).1

variable (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)

/-- The original level homeomorphisms form a natural isomorphism along full upper preimages. -/
def stageNatIso :
    curvePlaceFixedModelPointDiagram k K
      (curvePlacePrincipalExceptional k K s (t : K))
      (affineChartWeilRestriction
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y) ≅
      curveUpperLevelFunctor k K L s t ⋙
        curvePlaceFixedModelPointDiagram k L
          (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K))) Y := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  refine NatIso.ofComponents (fun T => by
    letI := curvePlaceFixedModelStageTopology k K
      (curvePlacePrincipalExceptional k K s (t : K))
      (affineChartWeilRestriction
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y) T
    letI := curvePlaceFixedModelStageTopology k L
      (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))) Y (upperLevel k K L s t T)
    exact (adelicLevelPointHomeomorph k K L s t T Y n j hj).toEquiv.toIso) ?_
  intro T U f
  ext p
  exact CurvePlaceFixedLevelWeilEvaluation.levelPoint_natural
    k K L s t T Y n j hj U (leOfHom f) p

/-- Original fixed-model Weil restriction commutes with actual full curve adeles and their topologies. -/
def adelicPointHomeomorph :
    @Homeomorph
      (CurvePlaceFixedModelAdelePoints k K
        (curvePlacePrincipalExceptional k K s (t : K))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y))
      (CurvePlaceFixedModelAdelePoints k L
        (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) Y)
      (curvePlaceFixedModelAdelePointTopology k K
        (curvePlacePrincipalExceptional k K s (t : K))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y))
      (curvePlaceFixedModelAdelePointTopology k L
        (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) Y) := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : IsNoetherianRing (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) :=
    IsNoetherianRing.of_finite
      (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _
  exact finalCoconeHomeomorph
    (curvePlaceFixedModelPointDiagram k K
      (curvePlacePrincipalExceptional k K s (t : K))
      (affineChartWeilRestriction
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y))
    (curvePlaceFixedModelPointDiagram k L
      (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))) Y)
    (curveUpperLevelFunctor k K L s t)
    (ringPointCocone
      (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (curvePlaceAdeleLevelOverDiagram k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceAdeleOverCocone k K (curvePlacePrincipalExceptional k K s (t : K))))
    (ringPointCocone
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))))
      (curvePlaceAdeleLevelOverDiagram k L
        (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (curvePlaceAdeleOverCocone k L
        (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))))
    (pointCoconeIsColimit k K (curvePlacePrincipalExceptional k K s (t : K)) _)
    (pointCoconeIsColimit k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))) Y)
    (stageNatIso k K L s t Y n j hj)
    (curvePlaceFixedModelStageTopology k K (curvePlacePrincipalExceptional k K s (t : K)) _)
    (curvePlaceFixedModelStageTopology k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))) Y)
    (fun f => upperTransition_continuous k K L s t Y f)
    (fun T => by
      let := curvePlaceFixedModelStageTopology k K
        (curvePlacePrincipalExceptional k K s (t : K))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y) T
      let := curvePlaceFixedModelStageTopology k L
        (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) Y (upperLevel k K L s t T)
      exact (adelicLevelPointHomeomorph k K L s t T Y n j hj).isHomeomorph)

/-- On every original enlarged support, the full comparison is the original level comparison. -/
@[simp]
theorem adelicPointHomeomorph_stage
    (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))
    (p : RingPoint
      (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :
    letI : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
    letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
    adelicPointHomeomorph k K L s t Y n j hj
      (p.changeRing (curvePlaceAdeleLevelOverι k K
        (curvePlacePrincipalExceptional k K s (t : K)) T).hom) =
      (adelicLevelPointHomeomorph k K L s t T Y n j hj p).changeRing
        (curvePlaceAdeleLevelOverι k L
          (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T)).hom := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  unfold adelicPointHomeomorph
  apply finalCoconeHomeomorph_ι

end Langlands.Global.CurvePlaceFixedModelWeilHomeomorph
