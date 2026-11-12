import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps
import Langlands.Global.AdelicSpaceLevelTopologyProof
import Langlands.Global.AdelicSpacePointTopologyStatement
import Langlands.Topology.FinalStageTopology

/-!
# Morphisms on adelic points of separated algebraic spaces

Conrad, printed p.17: a morphism `f : X → Y` of separated algebraic spaces of finite type over
the `S`-integers of a global field induces a continuous map `X(𝔸) → Y(𝔸)`, and a closed
embedding when `f` is a closed immersion. The proof goes through three layers.

* On each local factor of a level, this is functoriality of the étale-chart topology over a
  henselian valued field.
* On a level, the coordinate maps are homeomorphisms onto products of factors
  (Proposition 5.2).
* On the full adelic points, which carry the final topology of the levels, continuity holds
  levelwise. For a closed immersion, a level point whose image comes from `X(𝔸)` already comes
  from the same level of `X`, because the level is a subring of the adeles.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointTopologyFacts
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)
open NumberField (RingOfIntegers)

namespace Langlands.Global

namespace AdelicSpacePointMapsProof

open AdelicSpaceLocalFields AdelicSpaceLevelFactors

section NumberField

variable (K : Type u) [Field K] [NumberField K]

section Level

variable (T : Finset (FinitePlace K))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K)))}

/-- Morphisms are continuous on every factor of a number-field level. -/
theorem numberField_factor_continuous (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y)
    (i : NumberFieldLevelFactorIndex K T) :
    @Continuous _ _ (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K T i))
      (fieldValuedPointTopology _ Y (numberFieldLevelFieldAlgHom K T i)) (RingPoints.map f) := by
  rcases i with v | v | v
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inl v)) := infiniteNormedField K v
    exact @continuous_fieldValued _ _ X Y _ _ _ _ N (instAdelicSpaceLevelTopology6 K T (.inl v))
      (infinite_isHenselianValuedField K v) hY hftY f _
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inl v))) :=
      normedField (RingOfIntegers K) K v.1
    exact @continuous_fieldValued _ _ X Y _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inr (.inl v)))
      (isHenselianValuedField (RingOfIntegers K) K v.1) hY hftY f _
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inr v))) :=
      normedField (RingOfIntegers K) K v.1
    exact @continuous_fieldValued _ _ X Y _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inr (.inr v)))
      (isHenselianValuedField (RingOfIntegers K) K v.1) hY hftY f _

/-- Closed immersions are closed embeddings on every factor of a number-field level. -/
theorem numberField_factor_closed (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) X) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion (hom f)) (i : NumberFieldLevelFactorIndex K T) :
    @IsClosedEmbedding _ _ (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K T i))
      (fieldValuedPointTopology _ Y (numberFieldLevelFieldAlgHom K T i)) (RingPoints.map f) := by
  rcases i with v | v | v
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inl v)) := infiniteNormedField K v
    exact @isClosedEmbedding_fieldValued _ _ X Y _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inl v))
      (infinite_isHenselianValuedField K v) hX hftX hY hftY f hf _ Function.injective_id
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inl v))) :=
      normedField (RingOfIntegers K) K v.1
    exact @isClosedEmbedding_fieldValued _ _ X Y _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inr (.inl v)))
      (isHenselianValuedField (RingOfIntegers K) K v.1) hX hftX hY hftY f hf _
      Function.injective_id
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inr v))) :=
      normedField (RingOfIntegers K) K v.1
    exact @isClosedEmbedding_fieldValued _ _ X Y _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inr (.inr v)))
      (isHenselianValuedField (RingOfIntegers K) K v.1) hX hftX hY hftY f hf _
      Subtype.val_injective

/-- Morphisms are continuous on number-field levels. -/
theorem numberField_level_continuous (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y) :
    @Continuous _ _ (numberFieldSpaceLevelTopology K T X) (numberFieldSpaceLevelTopology K T Y)
      (RingPoints.map f) :=
  continuous_coordinate _ _ _ _ f (numberField_factor_continuous K T hY hftY f)

/-- Closed immersions are closed embeddings on number-field levels. -/
theorem numberField_level_closed (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) X) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion (hom f)) :
    @IsClosedEmbedding _ _ (numberFieldSpaceLevelTopology K T X)
      (numberFieldSpaceLevelTopology K T Y) (RingPoints.map f) :=
  isClosedEmbedding_coordinate _ _ _ _ f (numberFieldSpaceLevelPoints K T X hX hftX)
    (numberFieldSpaceLevelPoints K T Y hY hftY)
    (numberField_factor_closed K T hX hftX hY hftY f hf)

end Level

variable (S : Finset (FinitePlace K))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- The base change of a morphism to the `T`-integers. -/
def numberFieldLevelMap (T : AdelicLevelIndexAbove S) (f : X ⟶ Y) :
    numberFieldSpaceLevelBaseChange K T.property X ⟶ numberFieldSpaceLevelBaseChange K T.property Y :=
  baseChangeMap _ f

/-- The stage identification is natural in morphisms. -/
theorem numberField_stageEquiv_map (T : AdelicLevelIndexAbove S) (f : X ⟶ Y)
    (p : RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    numberFieldSpaceStageEquiv K S Y T (RingPoints.map f p) =
      RingPoints.map (numberFieldLevelMap K S T f) (numberFieldSpaceStageEquiv K S X T p) := by
  let _ : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let _ : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs
      (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) Y).symm
        (RingPoints.map f p) =
    RingPoints.map (baseChangeMap (Spec.algebraMap ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K)) f)
      ((baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
        ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]

/-- The stage identification is a homeomorphism. -/
theorem numberField_stageEquiv_isHomeomorph (T : AdelicLevelIndexAbove S) :
    @IsHomeomorph _ _ (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X))
      (numberFieldSpaceStageEquiv K S X T) := by
  let _ := numberFieldSpaceStageTopology K S X T
  let _ := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X)
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨⟨⟨rfl⟩, (numberFieldSpaceStageEquiv K S X T).injective⟩,
      (numberFieldSpaceStageEquiv K S X T).surjective⟩

/-- Morphisms are continuous on number-field stages. -/
theorem numberField_stage_continuous (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y)
    (T : AdelicLevelIndexAbove S) :
    @Continuous _ _ (numberFieldSpaceStageTopology K S X T) (numberFieldSpaceStageTopology K S Y T)
      (RingPoints.map f) := by
  let _ := numberFieldSpaceStageTopology K S X T
  let _ := numberFieldSpaceStageTopology K S Y T
  let _ := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X)
  let _ := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property Y)
  have hX := numberField_stageEquiv_isHomeomorph K S (X := X) T
  have hY' := numberField_stageEquiv_isHomeomorph K S (X := Y) T
  rw [hY'.isInducing.continuous_iff]
  have hcomm : numberFieldSpaceStageEquiv K S Y T ∘ RingPoints.map f =
      RingPoints.map (numberFieldLevelMap K S T f) ∘ numberFieldSpaceStageEquiv K S X T :=
    funext (numberField_stageEquiv_map K S T f)
  rw [hcomm]
  exact (numberField_level_continuous K T.val
    (X := numberFieldSpaceLevelBaseChange K T.property X)
    (Y := numberFieldSpaceLevelBaseChange K T.property Y) hY.baseChange
    (finiteTypeOverRing_baseChange _ hftY) _).comp
    hX.continuous

/-- Closed immersions are closed embeddings on number-field stages. -/
theorem numberField_stage_closed (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion (hom f)) (T : AdelicLevelIndexAbove S) :
    @IsClosedEmbedding _ _ (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceStageTopology K S Y T) (RingPoints.map f) := by
  let _ := numberFieldSpaceStageTopology K S X T
  let _ := numberFieldSpaceStageTopology K S Y T
  let _ := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X)
  let _ := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property Y)
  have hX' := numberField_stageEquiv_isHomeomorph K S (X := X) T
  have hY' := numberField_stageEquiv_isHomeomorph K S (X := Y) T
  rw [← hY'.isClosedEmbedding.of_comp_iff]
  have hcomm : numberFieldSpaceStageEquiv K S Y T ∘ RingPoints.map f =
      RingPoints.map (numberFieldLevelMap K S T f) ∘ numberFieldSpaceStageEquiv K S X T :=
    funext (numberField_stageEquiv_map K S T f)
  rw [hcomm]
  exact (numberField_level_closed K T.val
    (X := numberFieldSpaceLevelBaseChange K T.property X)
    (Y := numberFieldSpaceLevelBaseChange K T.property Y) hX.baseChange
    (finiteTypeOverRing_baseChange _ hftX) hY.baseChange (finiteTypeOverRing_baseChange _ hftY) _
    (isClosedImmersion_baseChangeMap _ f hf)).comp hX'.isClosedEmbedding

/-- The inclusion of a level in the adeles is injective. -/
theorem numberField_levelι_injective (T : AdelicLevelIndexAbove S) :
    Function.Injective (numberFieldAdeleLevelOverι K S T).hom :=
  fun _ _ h => Subtype.ext h

/-- **Continuity**, number fields. -/
theorem numberField_continuous (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y) :
    @Continuous _ _ (numberFieldSpaceAdelePointTopology K S X)
      (numberFieldSpaceAdelePointTopology K S Y) (RingPoints.map f) :=
  @Topology.FinalStage.continuous_of_stages _ _ (numberFieldSpaceStageTopology K S X) _
    (numberFieldSpaceStageMap K S X) _ (numberFieldSpaceStageTopology K S Y) _
    (numberFieldSpaceStageMap K S Y) (RingPoints.map f) (fun _ => RingPoints.map f)
    (numberField_stage_continuous K S hY hftY f)
    (fun T x => (RingPoints.changeRing_map f (numberFieldAdeleLevelOverι K S T).hom x).symm)

/-- **Closed immersions give closed embeddings**, number fields. -/
theorem numberField_closed (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion (hom f)) :
    @IsClosedEmbedding _ _ (numberFieldSpaceAdelePointTopology K S X)
      (numberFieldSpaceAdelePointTopology K S Y) (RingPoints.map f) := by
  refine @Topology.FinalStage.isClosedEmbedding_of_stages _ _ (numberFieldSpaceStageTopology K S X)
    _ (numberFieldSpaceStageMap K S X) _ (numberFieldSpaceStageTopology K S Y) _
    (numberFieldSpaceStageMap K S Y) (RingPoints.map f) (fun _ => RingPoints.map f)
    (numberField_stage_closed K S hX hftX hY hftY f hf)
    (fun T x => (RingPoints.changeRing_map f (numberFieldAdeleLevelOverι K S T).hom x).symm)
    (ClosedImmersionPoints.map_injective f hf) ?_
  rintro T y ⟨x, hx⟩
  obtain ⟨x', -, hx'⟩ := ClosedImmersionPoints.exists_changeRing_eq f hf
    (numberFieldAdeleLevelOverι K S T).hom (numberField_levelι_injective K S T) hx
  exact ⟨x', hx'⟩

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

section Level

variable (T : Finset (AlgebraicCurve.Place k F))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F T)))}

/-- Morphisms are continuous on every factor of a curve-place level. -/
theorem curve_factor_continuous (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F T) Y) (f : X ⟶ Y)
    (i : CurvePlaceLevelFactorIndex k F T) :
    @Continuous _ _ (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F T i))
      (fieldValuedPointTopology _ Y (curvePlaceLevelFieldAlgHom k F T i)) (RingPoints.map f) := by
  rcases i with v | v
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inl v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    exact @continuous_fieldValued _ _ X Y _ _ _ _ N (instAdelicSpaceLevelTopology3 k F T (.inl v))
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum) hY hftY f _
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inr v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    exact @continuous_fieldValued _ _ X Y _ _ _ _ N (instAdelicSpaceLevelTopology3 k F T (.inr v))
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum) hY hftY f _

/-- Closed immersions are closed embeddings on every factor of a curve-place level. -/
theorem curve_factor_closed (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F T) X) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F T) Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion (hom f)) (i : CurvePlaceLevelFactorIndex k F T) :
    @IsClosedEmbedding _ _ (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F T i))
      (fieldValuedPointTopology _ Y (curvePlaceLevelFieldAlgHom k F T i)) (RingPoints.map f) := by
  rcases i with v | v
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inl v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    exact @isClosedEmbedding_fieldValued _ _ X Y _ _ _ _ N
      (instAdelicSpaceLevelTopology3 k F T (.inl v))
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum) hX hftX hY hftY f hf
      _ Function.injective_id
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inr v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    exact @isClosedEmbedding_fieldValued _ _ X Y _ _ _ _ N
      (instAdelicSpaceLevelTopology3 k F T (.inr v))
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum) hX hftX hY hftY f hf
      _ Subtype.val_injective

/-- Morphisms are continuous on curve-place levels. -/
theorem curve_level_continuous (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F T) Y) (f : X ⟶ Y) :
    @Continuous _ _ (curvePlaceSpaceLevelTopology k F T X) (curvePlaceSpaceLevelTopology k F T Y)
      (RingPoints.map f) :=
  continuous_coordinate _ _ _ _ f (curve_factor_continuous k F T hY hftY f)

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- Closed immersions are closed embeddings on curve-place levels, for nonempty `T`. -/
theorem curve_level_closed (hT : T.Nonempty) (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F T) X) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F T) Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion (hom f)) :
    @IsClosedEmbedding _ _ (curvePlaceSpaceLevelTopology k F T X)
      (curvePlaceSpaceLevelTopology k F T Y) (RingPoints.map f) :=
  isClosedEmbedding_coordinate _ _ _ _ f (curvePlaceSpaceLevelPoints k F T hT X hX hftX)
    (curvePlaceSpaceLevelPoints k F T hT Y hY hftY)
    (curve_factor_closed k F T hX hftX hY hftY f hf)

end Level

variable (S : Finset (AlgebraicCurve.Place k F))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- The base change of a morphism to the `T`-integers. -/
def curveLevelMap (T : AdelicLevelIndexAbove S) (f : X ⟶ Y) :
    curvePlaceSpaceLevelBaseChange k F T.property X ⟶
      curvePlaceSpaceLevelBaseChange k F T.property Y :=
  baseChangeMap _ f

/-- The stage identification is natural in morphisms. -/
theorem curve_stageEquiv_map (T : AdelicLevelIndexAbove S) (f : X ⟶ Y)
    (p : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    curvePlaceSpaceStageEquiv k F S Y T (RingPoints.map f p) =
      RingPoints.map (curveLevelMap k F S T f) (curvePlaceSpaceStageEquiv k F S X T p) := by
  let _ : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let _ : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  have : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) Y).symm (RingPoints.map f p) =
    RingPoints.map (baseChangeMap (Spec.algebraMap (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val)) f)
      ((baseChangeRingPointsEquiv (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
        (curvePlaceAdeleLevelOver k F S T) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]

/-- The stage identification is a homeomorphism. -/
theorem curve_stageEquiv_isHomeomorph (T : AdelicLevelIndexAbove S) :
    @IsHomeomorph _ _ (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X))
      (curvePlaceSpaceStageEquiv k F S X T) := by
  let _ := curvePlaceSpaceStageTopology k F S X T
  let _ := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X)
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨⟨⟨rfl⟩, (curvePlaceSpaceStageEquiv k F S X T).injective⟩,
      (curvePlaceSpaceStageEquiv k F S X T).surjective⟩

/-- Morphisms are continuous on curve-place stages. -/
theorem curve_stage_continuous (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y) (f : X ⟶ Y)
    (T : AdelicLevelIndexAbove S) :
    @Continuous _ _ (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceStageTopology k F S Y T) (RingPoints.map f) := by
  let _ := curvePlaceSpaceStageTopology k F S X T
  let _ := curvePlaceSpaceStageTopology k F S Y T
  let _ := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X)
  let _ := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property Y)
  have hX := curve_stageEquiv_isHomeomorph k F S (X := X) T
  have hY' := curve_stageEquiv_isHomeomorph k F S (X := Y) T
  rw [hY'.isInducing.continuous_iff]
  have hcomm : curvePlaceSpaceStageEquiv k F S Y T ∘ RingPoints.map f =
      RingPoints.map (curveLevelMap k F S T f) ∘ curvePlaceSpaceStageEquiv k F S X T :=
    funext (curve_stageEquiv_map k F S T f)
  rw [hcomm]
  exact (curve_level_continuous k F T.val
    (X := curvePlaceSpaceLevelBaseChange k F T.property X)
    (Y := curvePlaceSpaceLevelBaseChange k F T.property Y) hY.baseChange
    (finiteTypeOverRing_baseChange _ hftY) _).comp hX.continuous

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- Closed immersions are closed embeddings on curve-place stages. -/
theorem curve_stage_closed (hS : S.Nonempty) (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion (hom f)) (T : AdelicLevelIndexAbove S) :
    @IsClosedEmbedding _ _ (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceStageTopology k F S Y T) (RingPoints.map f) := by
  let _ := curvePlaceSpaceStageTopology k F S X T
  let _ := curvePlaceSpaceStageTopology k F S Y T
  let _ := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X)
  let _ := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property Y)
  have hX' := curve_stageEquiv_isHomeomorph k F S (X := X) T
  have hY' := curve_stageEquiv_isHomeomorph k F S (X := Y) T
  rw [← hY'.isClosedEmbedding.of_comp_iff]
  have hcomm : curvePlaceSpaceStageEquiv k F S Y T ∘ RingPoints.map f =
      RingPoints.map (curveLevelMap k F S T f) ∘ curvePlaceSpaceStageEquiv k F S X T :=
    funext (curve_stageEquiv_map k F S T f)
  rw [hcomm]
  exact (curve_level_closed k F T.val (X := curvePlaceSpaceLevelBaseChange k F T.property X)
    (Y := curvePlaceSpaceLevelBaseChange k F T.property Y) (hS.mono T.property) hX.baseChange
    (finiteTypeOverRing_baseChange _ hftX) hY.baseChange (finiteTypeOverRing_baseChange _ hftY) _
    (isClosedImmersion_baseChangeMap _ f hf)).comp hX'.isClosedEmbedding

/-- The inclusion of a level in the adeles is injective. -/
theorem curve_levelι_injective (T : AdelicLevelIndexAbove S) :
    Function.Injective (curvePlaceAdeleLevelOverι k F S T).hom :=
  fun _ _ h => Subtype.ext h

/-- **Continuity**, global function fields. -/
theorem curve_continuous (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y) (f : X ⟶ Y) :
    @Continuous _ _ (curvePlaceSpaceAdelePointTopology k F S X)
      (curvePlaceSpaceAdelePointTopology k F S Y) (RingPoints.map f) :=
  @Topology.FinalStage.continuous_of_stages _ _ (curvePlaceSpaceStageTopology k F S X) _
    (curvePlaceSpaceStageMap k F S X) _ (curvePlaceSpaceStageTopology k F S Y) _
    (curvePlaceSpaceStageMap k F S Y) (RingPoints.map f) (fun _ => RingPoints.map f)
    (curve_stage_continuous k F S hY hftY f)
    (fun T x => (RingPoints.changeRing_map f (curvePlaceAdeleLevelOverι k F S T).hom x).symm)

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- **Closed immersions give closed embeddings**, global function fields. -/
theorem curve_closed (hS : S.Nonempty) (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion (hom f)) :
    @IsClosedEmbedding _ _ (curvePlaceSpaceAdelePointTopology k F S X)
      (curvePlaceSpaceAdelePointTopology k F S Y) (RingPoints.map f) := by
  refine @Topology.FinalStage.isClosedEmbedding_of_stages _ _
    (curvePlaceSpaceStageTopology k F S X) _ (curvePlaceSpaceStageMap k F S X) _
    (curvePlaceSpaceStageTopology k F S Y) _ (curvePlaceSpaceStageMap k F S Y) (RingPoints.map f)
    (fun _ => RingPoints.map f) (curve_stage_closed k F S hS hX hftX hY hftY f hf)
    (fun T x => (RingPoints.changeRing_map f (curvePlaceAdeleLevelOverι k F S T).hom x).symm)
    (ClosedImmersionPoints.map_injective f hf) ?_
  rintro T y ⟨x, hx⟩
  obtain ⟨x', -, hx'⟩ := ClosedImmersionPoints.exists_changeRing_eq f hf
    (curvePlaceAdeleLevelOverι k F S T).hom (curve_levelι_injective k F S T) hx
  exact ⟨x', hx'⟩

end Curve

end AdelicSpacePointMapsProof

end Langlands.Global
