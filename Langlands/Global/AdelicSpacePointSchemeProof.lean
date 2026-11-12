import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeSpacePointComparison
import Langlands.Global.AdelicSpaceLevelTopologyProof
import Langlands.Global.AdelicSpacePointTopologyStatement
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.Global.AdelicLevelModelTransitionLocal
import Langlands.Topology.FinalStageTopology

/-!
# Adelic points of schemes viewed as algebraic spaces

Conrad, printed p.17: for a separated scheme of finite type over the `S`-integers of a global
field, the topology on the adelic points of the associated algebraic space is the published
topology on the adelic points of the scheme. Both are final topologies for the same stages.
On each stage, the comparison reduces factor by factor to two facts. Over a local field, the
étale-chart topology of a scheme is its scheme topology. On the completed valuation ring, the
scheme topology is induced from the completion.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeSpacePointComparison
open Langlands.AlgebraicGeometry.PointTopology (RingPoint ringBaseChange ringPointBaseChangeEquiv
  schemePointTopology IsHenselianValuedField)
open NumberField (RingOfIntegers)

namespace Langlands.Global

namespace AdelicSpacePointSchemeProof

open AdelicSpaceLocalFields

/-- Base change keeps local finite type and separatedness of schemes. -/
theorem baseChange_instances {S T : Scheme.{u}} (g : T ⟶ S) (U : Over S)
    [LocallyOfFiniteType U.hom] [_root_.AlgebraicGeometry.IsSeparated U.hom] :
    LocallyOfFiniteType ((Over.pullback g).obj U).hom ∧
      _root_.AlgebraicGeometry.IsSeparated ((Over.pullback g).obj U).hom :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback U.hom g) (inferInstanceAs (LocallyOfFiniteType U.hom)),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsSeparated)
      (IsPullback.of_hasPullback U.hom g)
      (inferInstanceAs (_root_.AlgebraicGeometry.IsSeparated U.hom))⟩

section NumberField

variable (K : Type u) [Field K] [NumberField K]

section Level

variable (T : Finset (FinitePlace K))
  (V : Over (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K))))
  [LocallyOfFiniteType V.hom] [_root_.AlgebraicGeometry.IsSeparated V.hom]

/-- Every factor of a number-field level compares the space and scheme topologies. -/
theorem numberField_factor (i : NumberFieldLevelFactorIndex K T) :
    @IsHomeomorph _ _
      (fieldValuedPointTopology _ ((schemeToSpace _).obj V) (numberFieldLevelFieldAlgHom K T i))
      (schemePointTopology (NumberFieldLevelFactor K T i)
        (ringBaseChange _ (NumberFieldLevelFactor K T i) V) (NumberFieldLevelFactor K T i))
      (fun p => ringPointBaseChangeEquiv _ (NumberFieldLevelFactor K T i)
        (NumberFieldLevelFactor K T i) V (schemeRingPointsEquiv _ V _ p)) := by
  have hu : IsOpenUnits (NumberFieldLevelFactor K T i) := adelicLocalFactorUnits.2 K T i
  have hr : _root_.IsReduced (NumberFieldLevelFactor K T i) := numberFieldLevelFactor_isReduced K i
  rcases i with v | v | v
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inl v)) := infiniteNormedField K v
    exact @isHomeomorph_localFactor _ _ V _ N (instAdelicSpaceLevelTopology6 K T (.inl v)) _ _ _
      _ _ _ hu hr (infinite_isHenselianValuedField K v) _ _ _ IsOpenEmbedding.id
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inl v))) :=
      normedField (RingOfIntegers K) K v.1
    exact @isHomeomorph_localFactor _ _ V _ N (instAdelicSpaceLevelTopology6 K T (.inr (.inl v)))
      _ _ _ _ _ _ hu hr (isHenselianValuedField (RingOfIntegers K) K v.1) _ _ _
      IsOpenEmbedding.id
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inr v))) :=
      normedField (RingOfIntegers K) K v.1
    exact @isHomeomorph_localFactor _ _ V _ N (instAdelicSpaceLevelTopology6 K T (.inr (.inr v)))
      _ _ _ _ _ _ hu hr (isHenselianValuedField (RingOfIntegers K) K v.1) _ _ _
      (show IsOpen ((v.1.adicCompletionIntegers K : ValuationSubring (v.1.adicCompletion K)) :
        Set (v.1.adicCompletion K)) from Valued.isOpen_valuationSubring _).isOpenEmbedding_subtypeVal

/-- **Levels**: on a number-field level, the space topology is the scheme topology. -/
theorem numberField_level :
    @IsHomeomorph _ _ (numberFieldSpaceLevelTopology K T ((schemeToSpace _).obj V))
      (numberFieldLevelModelPointTopology K T V) (schemeRingPointsEquiv _ V _) :=
  isHomeomorph_coordinate V _ _ (numberFieldLevelFieldAlgHom K T) (numberFieldLevelFactorAlgHom K T)
    (numberField_factor K T V)

end Level

variable (S : Finset (FinitePlace K))
  (U : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
  [LocallyOfFiniteType U.hom] [_root_.AlgebraicGeometry.IsSeparated U.hom]

/-- **Stages**: on each number-field stage, the space topology is the scheme topology. -/
theorem numberField_stage (T : AdelicLevelIndexAbove S) :
    @IsHomeomorph _ _ (numberFieldSpaceStageTopology K S ((schemeToSpace _).obj U) T)
      (numberFieldFixedModelStageTopology K S U T) (schemeRingPointsEquiv _ U _) := by
  let g := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property))
  let W := (schemeToSpace _).obj U
  let UT := numberFieldLevelModelBaseChange K T.property U
  have hUT := baseChange_instances g U
  have : LocallyOfFiniteType UT.hom := hUT.1
  have : _root_.AlgebraicGeometry.IsSeparated UT.hom := hUT.2
  let ψ : RingPoints ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldSpaceLevelBaseChange K T.property W) (numberFieldAdeleLevel K T.val) →
      RingPoints ((T.val : Set (FinitePlace K)).integer K) ((schemeToSpace _).obj UT)
        (numberFieldAdeleLevel K T.val) :=
    RingPoints.map (baseChangeSchemeIso g U).inv
  have hlev := numberField_level K T.val UT
  have hiso := isHomeomorph_coordinate_iso (A := numberFieldAdeleLevel K T.val)
    (NumberFieldLevelFactor K T.val) (NumberFieldLevelField K T.val)
    (numberFieldLevelFieldAlgHom K T.val) (numberFieldLevelFactorAlgHom K T.val)
    (baseChangeSchemeIso g U).symm
  have e₁ : numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property W) =
      TopologicalSpace.induced ψ (numberFieldSpaceLevelTopology K T.val ((schemeToSpace _).obj UT)) := by
    let _ := numberFieldSpaceLevelTopology K T.val (baseChange g W)
    let _ := numberFieldSpaceLevelTopology K T.val ((schemeToSpace _).obj ((Over.pullback g).obj U))
    exact hiso.isInducing.eq_induced
  have e₂ : numberFieldSpaceLevelTopology K T.val ((schemeToSpace _).obj UT) =
      TopologicalSpace.induced (schemeRingPointsEquiv _ UT _)
        (numberFieldLevelModelPointTopology K T.val UT) := by
    let _ := numberFieldSpaceLevelTopology K T.val ((schemeToSpace _).obj UT)
    let _ := numberFieldLevelModelPointTopology K T.val UT
    exact hlev.isInducing.eq_induced
  apply SchemeSpacePointComparison.isHomeomorph_of_eq_induced
  rw [numberFieldSpaceStageTopology, e₁, e₂, induced_compose, induced_compose,
    numberFieldFixedModelStageTopology, induced_compose]
  congr 1

/-- **Conrad's p.17 scheme comparison, number fields.** -/
theorem numberField_scheme :
    @IsHomeomorph _ _ (numberFieldSpaceAdelePointTopology K S ((schemeToSpace _).obj U))
      (numberFieldFixedModelAdelePointTopology K S U)
      (schemeRingPointsEquiv ((S : Set (FinitePlace K)).integer K) U (numberFieldAdeleOver K S)) :=
  @Topology.FinalStage.isHomeomorph_of_stages _ _
    (numberFieldSpaceStageTopology K S ((schemeToSpace _).obj U)) _
    (numberFieldSpaceStageMap K S ((schemeToSpace _).obj U)) _
    (numberFieldFixedModelStageTopology K S U) _
    (fun T p => p.changeRing (numberFieldAdeleLevelOverι K S T).hom)
    (schemeRingPointsEquiv _ U _) (fun _ => schemeRingPointsEquiv _ U _)
    (numberField_stage K S U) (fun _ _ => rfl) (schemeRingPointsEquiv _ U _).bijective

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

section Level

variable (T : Finset (AlgebraicCurve.Place k F))
  (V : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T))))
  [LocallyOfFiniteType V.hom] [_root_.AlgebraicGeometry.IsSeparated V.hom]

/-- Every factor of a curve-place level compares the space and scheme topologies. -/
theorem curve_factor (i : CurvePlaceLevelFactorIndex k F T) :
    @IsHomeomorph _ _
      (fieldValuedPointTopology _ ((schemeToSpace _).obj V) (curvePlaceLevelFieldAlgHom k F T i))
      (schemePointTopology (CurvePlaceLevelFactor k F T i)
        (ringBaseChange _ (CurvePlaceLevelFactor k F T i) V) (CurvePlaceLevelFactor k F T i))
      (fun p => ringPointBaseChangeEquiv _ (CurvePlaceLevelFactor k F T i)
        (CurvePlaceLevelFactor k F T i) V (schemeRingPointsEquiv _ V _ p)) := by
  have hu : IsOpenUnits (CurvePlaceLevelFactor k F T i) := adelicLocalFactorUnits.1 k F T i
  have hr : _root_.IsReduced (CurvePlaceLevelFactor k F T i) := curvePlaceLevelFactor_isReduced k F i
  rcases i with v | v
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inl v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    exact @isHomeomorph_localFactor _ _ V _ N (instAdelicSpaceLevelTopology3 k F T (.inl v))
      _ _ _ _ _ _ hu hr (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum)
      _ _ _ IsOpenEmbedding.id
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inr v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    exact @isHomeomorph_localFactor _ _ V _ N (instAdelicSpaceLevelTopology3 k F T (.inr v))
      _ _ _ _ _ _ hu hr (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum)
      _ _ _ (show IsOpen ((v.1.heightOneSpectrum.adicCompletionIntegers F :
        ValuationSubring (v.1.heightOneSpectrum.adicCompletion F)) :
          Set (v.1.heightOneSpectrum.adicCompletion F)) from
        Valued.isOpen_valuationSubring _).isOpenEmbedding_subtypeVal

/-- **Levels**: on a curve-place level, the space topology is the scheme topology. -/
theorem curve_level :
    @IsHomeomorph _ _ (curvePlaceSpaceLevelTopology k F T ((schemeToSpace _).obj V))
      (curvePlaceLevelModelPointTopology k F T V) (schemeRingPointsEquiv _ V _) :=
  isHomeomorph_coordinate V _ _ (curvePlaceLevelFieldAlgHom k F T) (curvePlaceLevelFactorAlgHom k F T)
    (curve_factor k F T V)

end Level

variable (S : Finset (AlgebraicCurve.Place k F))
  (U : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
  [LocallyOfFiniteType U.hom] [_root_.AlgebraicGeometry.IsSeparated U.hom]

/-- **Stages**: on each curve-place stage, the space topology is the scheme topology. -/
theorem curve_stage (T : AdelicLevelIndexAbove S) :
    @IsHomeomorph _ _ (curvePlaceSpaceStageTopology k F S ((schemeToSpace _).obj U) T)
      (curvePlaceFixedModelStageTopology k F S U T) (schemeRingPointsEquiv _ U _) := by
  let g := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property))
  let W := (schemeToSpace _).obj U
  let UT := curvePlaceLevelModelBaseChange k F T.property U
  have hUT := baseChange_instances g U
  have : LocallyOfFiniteType UT.hom := hUT.1
  have : _root_.AlgebraicGeometry.IsSeparated UT.hom := hUT.2
  let ψ : RingPoints (curvePlaceSIntegers k F T.val)
      (curvePlaceSpaceLevelBaseChange k F T.property W) (curvePlaceAdeleLevel k F T.val) →
      RingPoints (curvePlaceSIntegers k F T.val) ((schemeToSpace _).obj UT)
        (curvePlaceAdeleLevel k F T.val) :=
    RingPoints.map (baseChangeSchemeIso g U).inv
  have hlev := curve_level k F T.val UT
  have hiso := isHomeomorph_coordinate_iso (A := curvePlaceAdeleLevel k F T.val)
    (CurvePlaceLevelFactor k F T.val) (CurvePlaceLevelField k F T.val)
    (curvePlaceLevelFieldAlgHom k F T.val) (curvePlaceLevelFactorAlgHom k F T.val)
    (baseChangeSchemeIso g U).symm
  have e₁ : curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property W) =
      TopologicalSpace.induced ψ (curvePlaceSpaceLevelTopology k F T.val ((schemeToSpace _).obj UT)) := by
    let _ := curvePlaceSpaceLevelTopology k F T.val (baseChange g W)
    let _ := curvePlaceSpaceLevelTopology k F T.val ((schemeToSpace _).obj ((Over.pullback g).obj U))
    exact hiso.isInducing.eq_induced
  have e₂ : curvePlaceSpaceLevelTopology k F T.val ((schemeToSpace _).obj UT) =
      TopologicalSpace.induced (schemeRingPointsEquiv _ UT _)
        (curvePlaceLevelModelPointTopology k F T.val UT) := by
    let _ := curvePlaceSpaceLevelTopology k F T.val ((schemeToSpace _).obj UT)
    let _ := curvePlaceLevelModelPointTopology k F T.val UT
    exact hlev.isInducing.eq_induced
  apply SchemeSpacePointComparison.isHomeomorph_of_eq_induced
  rw [curvePlaceSpaceStageTopology, e₁, e₂, induced_compose, induced_compose,
    curvePlaceFixedModelStageTopology, induced_compose]
  congr 1

/-- **Conrad's p.17 scheme comparison, global function fields.** -/
theorem curve_scheme :
    @IsHomeomorph _ _ (curvePlaceSpaceAdelePointTopology k F S ((schemeToSpace _).obj U))
      (curvePlaceFixedModelAdelePointTopology k F S U)
      (schemeRingPointsEquiv (curvePlaceSIntegers k F S) U (curvePlaceAdeleOver k F S)) :=
  @Topology.FinalStage.isHomeomorph_of_stages _ _
    (curvePlaceSpaceStageTopology k F S ((schemeToSpace _).obj U)) _
    (curvePlaceSpaceStageMap k F S ((schemeToSpace _).obj U)) _
    (curvePlaceFixedModelStageTopology k F S U) _
    (fun T p => p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom)
    (schemeRingPointsEquiv _ U _) (fun _ => schemeRingPointsEquiv _ U _)
    (curve_stage k F S U) (fun _ _ => rfl) (schemeRingPointsEquiv _ U _).bijective

end Curve

end AdelicSpacePointSchemeProof

open AdelicSpacePointSchemeProof in
/-- **Conrad's p.17 scheme comparison for number fields.** -/
theorem numberFieldSpaceAdelePointScheme : NumberFieldSpaceAdelePointSchemeStatement.{u} := by
  intro K _ _ S U _ _ _
  exact numberField_scheme K S U

open AdelicSpacePointSchemeProof in
/-- **Conrad's p.17 scheme comparison for global function fields.** -/
theorem curvePlaceSpaceAdelePointScheme : CurvePlaceSpaceAdelePointSchemeStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S _ U _ _ _
  exact curve_scheme k F S U

end Langlands.Global
