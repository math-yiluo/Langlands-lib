import Langlands.AlgebraicGeometry.AlgebraicSpace.CompleteFieldSmoothPointOpenStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Langlands.Global.AdelicSpaceModelOpenReduction
import Langlands.Global.AdelicSpaceLevelFactors

/-! # Local smooth openness and the actual adelic factors of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SmoothLocalOpenReduction

variable {C : Type u} [CommRing C]
  {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}
  {A K : Type u} [CommRing A] [Algebra C A] [Field K] [Algebra C K]

/-- The actual maps to generic-fibre points commute with a model morphism. -/
theorem fieldValuedPointMap_map (f : X ⟶ Y) (φ : A →ₐ[C] K)
    (p : RingPoints C X A) :
    fieldValuedPointMap C Y φ (RingPoints.map f p) =
      RingPoints.map (baseChangeMap (Spec.algebraMap C K) f)
        (fieldValuedPointMap C X φ p) := by
  apply (baseChangeRingPointsEquiv C K K Y).injective
  rw [fieldValuedPointMap, Equiv.apply_symm_apply, baseChangeRingPointsEquiv_map,
    fieldValuedPointMap, Equiv.apply_symm_apply, RingPoints.changeRing_map]

section Topological

variable [TopologicalSpace K]

/-- Openness over a field transfers along a bijective coefficient map. -/
theorem isOpenMap_fieldFactor (f : X ⟶ Y) (φ : A →ₐ[C] K)
    (hφ : Function.Bijective φ)
    (hopen : @IsOpenMap _ _ (etaleChartTopology K (baseChange (Spec.algebraMap C K) X))
      (etaleChartTopology K (baseChange (Spec.algebraMap C K) Y))
      (RingPoints.map (baseChangeMap (Spec.algebraMap C K) f))) :
    @IsOpenMap _ _ (fieldValuedPointTopology C X φ) (fieldValuedPointTopology C Y φ)
      (RingPoints.map f) := by
  let : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints C Y A) := fieldValuedPointTopology C Y φ
  let : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap C K) X) K) :=
    etaleChartTopology K (baseChange (Spec.algebraMap C K) X)
  let : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap C K) Y) K) :=
    etaleChartTopology K (baseChange (Spec.algebraMap C K) Y)
  have heX := CoordinatePointTopologyFacts.isHomeomorph_fieldValuedPointMap X φ hφ
  have heY := CoordinatePointTopologyFacts.isHomeomorph_fieldValuedPointMap Y φ hφ
  apply heY.isOpenEmbedding.isOpenMap_iff.mpr
  have hn : fieldValuedPointMap C Y φ ∘ RingPoints.map f =
      RingPoints.map (baseChangeMap (Spec.algebraMap C K) f) ∘ fieldValuedPointMap C X φ :=
    funext (fieldValuedPointMap_map f φ)
  rw [hn]
  exact hopen.comp heX.isOpenMap

end Topological

section Normed

variable {L : Type u} [NontriviallyNormedField L] [Algebra C L]
  (O : Subring L) [Algebra C O] [IsScalarTower C O L]

/-- Integral points of a separated locally finite-type space embed with open image. -/
theorem isOpenEmbedding_integerFactor
    (hO : ∀ x : L, x ∈ O ↔ ‖x‖ ≤ 1) (hhen : HenselianLocalRing O)
    (hX : IsSeparated X) (hlftX : LocallyOfFiniteTypeOverBase X) :
    @IsOpenEmbedding _ _ (fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O L))
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))
      (fieldValuedPointMap C X (IsScalarTower.toAlgHom C O L)) := by
  let : TopologicalSpace (RingPoints C X O) :=
    fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O L)
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  exact ⟨⟨fieldValuedPointMap_isInducing C X _,
    (baseChangeRingPointsEquiv C L L X).symm.injective.comp
      (RelativeIntegralPoints.changeRing_injective hX _ Subtype.val_injective)⟩,
    RelativeIntegralPoints.isOpen_range_fieldValuedPointMap O hO hhen
      (SpaceProductPoints.isQuasiSeparated_of_isSeparated hX) hlftX⟩

/-- The actual integral point map, bundled as a homeomorphism onto its open image. -/
def integerFactorHomeomorphRange
    (hO : ∀ x : L, x ∈ O ↔ ‖x‖ ≤ 1) (hhen : HenselianLocalRing O)
    (hX : IsSeparated X) (hlftX : LocallyOfFiniteTypeOverBase X) :
    letI : TopologicalSpace (RingPoints C X O) :=
      fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O L)
    letI : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
      etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
    RingPoints C X O ≃ₜ Set.range (fieldValuedPointMap C X (IsScalarTower.toAlgHom C O L)) := by
  let : TopologicalSpace (RingPoints C X O) :=
    fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O L)
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  exact (isOpenEmbedding_integerFactor O hO hhen hX hlftX).isEmbedding.toHomeomorph

/-- Open generic-fibre maps restrict to open maps on integral points. -/
theorem isOpenMap_integerFactor
    (hO : ∀ x : L, x ∈ O ↔ ‖x‖ ≤ 1) (hhen : HenselianLocalRing O)
    (hX : IsSeparated X) (hlftX : LocallyOfFiniteTypeOverBase X)
    (hY : IsSeparated Y) (hlftY : LocallyOfFiniteTypeOverBase Y) (f : X ⟶ Y)
    (hopen : @IsOpenMap _ _ (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) Y))
      (RingPoints.map (baseChangeMap (Spec.algebraMap C L) f))) :
    @IsOpenMap _ _ (fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O L))
      (fieldValuedPointTopology C Y (IsScalarTower.toAlgHom C O L)) (RingPoints.map f) := by
  let φ := IsScalarTower.toAlgHom C O L
  let : TopologicalSpace (RingPoints C X O) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints C Y O) := fieldValuedPointTopology C Y φ
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) Y) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) Y)
  have heX := (isOpenEmbedding_integerFactor O hO hhen hX hlftX).isOpenMap
  have heY := isOpenEmbedding_integerFactor O hO hhen hY hlftY
  apply heY.isOpenMap_iff.mpr
  have hn : fieldValuedPointMap C Y φ ∘ RingPoints.map f =
      RingPoints.map (baseChangeMap (Spec.algebraMap C L) f) ∘ fieldValuedPointMap C X φ :=
    funext (fieldValuedPointMap_map f φ)
  rw [hn]
  exact hopen.comp heX

variable [CompleteSpace L]

/-- The pending local smooth-openness theorem supplies the generic-fibre input. -/
theorem isOpenMap_genericFiber_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u})
    (hX : IsSeparated X) (hlftX : LocallyOfFiniteTypeOverBase X)
    (hY : IsSeparated Y) (hlftY : LocallyOfFiniteTypeOverBase Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) :
    @IsOpenMap _ _ (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) Y))
      (RingPoints.map (baseChangeMap (Spec.algebraMap C L) f)) :=
  hlocal L _ _ hX.baseChange hlftX.baseChange hY.baseChange hlftY.baseChange _
    hf.baseChangeMap

/-- Smooth openness in a field factor, conditional on the local theorem. -/
theorem isOpenMap_fieldFactor_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u})
    (hX : IsSeparated X) (hlftX : LocallyOfFiniteTypeOverBase X)
    (hY : IsSeparated Y) (hlftY : LocallyOfFiniteTypeOverBase Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) {R : Type u} [CommRing R] [Algebra C R]
    (φ : R →ₐ[C] L) (hφ : Function.Bijective φ) :
    @IsOpenMap _ _ (fieldValuedPointTopology C X φ) (fieldValuedPointTopology C Y φ)
      (RingPoints.map f) :=
  isOpenMap_fieldFactor f φ hφ
    (isOpenMap_genericFiber_of_smooth hlocal hX hlftX hY hlftY f hf)

/-- Smooth openness in an integer factor, conditional on the local theorem. -/
theorem isOpenMap_integerFactor_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u})
    (hO : ∀ x : L, x ∈ O ↔ ‖x‖ ≤ 1) (hhen : HenselianLocalRing O)
    (hX : IsSeparated X) (hlftX : LocallyOfFiniteTypeOverBase X)
    (hY : IsSeparated Y) (hlftY : LocallyOfFiniteTypeOverBase Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) :
    @IsOpenMap _ _ (fieldValuedPointTopology C X (IsScalarTower.toAlgHom C O L))
      (fieldValuedPointTopology C Y (IsScalarTower.toAlgHom C O L)) (RingPoints.map f) :=
  isOpenMap_integerFactor O hO hhen hX hlftX hY hlftY f
    (isOpenMap_genericFiber_of_smooth hlocal hX hlftX hY hlftY f hf)

end Normed

end SmoothLocalOpenReduction

end Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothLocalOpenReduction
open NumberField

set_option backward.isDefEq.respectTransparency false

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- Smooth local openness supplies openness at every actual curve-place factor. -/
theorem curvePlaceSpaceFactor_isOpenMap_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u})
    (hX : IsSeparated X) (hlftX : LocallyOfFiniteTypeOverBase X)
    (hY : IsSeparated Y) (hlftY : LocallyOfFiniteTypeOverBase Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (i : CurvePlaceLevelFactorIndex k F S) :
    @IsOpenMap _ _
      (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F S i))
      (fieldValuedPointTopology _ Y (curvePlaceLevelFieldAlgHom k F S i))
      (RingPoints.map f) := by
  rcases i with v | v
  · let : NontriviallyNormedField (CurvePlaceLevelField k F S (.inl v)) :=
      AdelicSpaceLocalFields.normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have : CompleteSpace (CurvePlaceLevelField k F S (.inl v)) :=
      AdelicSpaceLocalFields.completeSpace v.1.toValuationSubring F v.1.heightOneSpectrum
    let : Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F S (.inl v)) :=
      instAdelicSpaceLevelTopology3 k F S (.inl v)
    exact isOpenMap_fieldFactor_of_smooth (L := CurvePlaceLevelField k F S (.inl v))
      hlocal hX hlftX hY hlftY f hf
      (curvePlaceLevelFieldAlgHom k F S (.inl v)) Function.bijective_id
  · let : NontriviallyNormedField (CurvePlaceLevelField k F S (.inr v)) :=
      AdelicSpaceLocalFields.normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have : CompleteSpace (CurvePlaceLevelField k F S (.inr v)) :=
      AdelicSpaceLocalFields.completeSpace v.1.toValuationSubring F v.1.heightOneSpectrum
    let O : Subring (CurvePlaceLevelField k F S (.inr v)) :=
      (v.1.heightOneSpectrum.adicCompletionIntegers F).toSubring
    let : Algebra (curvePlaceSIntegers k F S) O :=
      instAdelicLevelModelPoints5 k F S (.inr v)
    let : Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F S (.inr v)) :=
      instAdelicSpaceLevelTopology3 k F S (.inr v)
    have : IsScalarTower (curvePlaceSIntegers k F S) O
        (CurvePlaceLevelField k F S (.inr v)) := ⟨fun c o x => by
      change ((algebraMap _ O c * o : O) : CurvePlaceLevelField k F S (.inr v)) * x =
        algebraMap _ (CurvePlaceLevelField k F S (.inr v)) c * ((o : _) * x)
      rw [Subring.coe_mul, mul_assoc]
      rfl⟩
    exact isOpenMap_integerFactor_of_smooth O hlocal
      (AdelicSpaceLocalFields.mem_adicCompletionIntegers_iff
        v.1.toValuationSubring F v.1.heightOneSpectrum)
      (AdelicSpaceLocalFields.henselianLocalRing
        v.1.toValuationSubring F v.1.heightOneSpectrum) hX hlftX hY hlftY f hf

/-- Smooth local openness and cofinite surjectivity give an open curve-place level map. -/
theorem curvePlaceSpaceLevel_isOpenMap_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f)
    (hs : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := CurvePlaceLevelFactor k F S i) f)) :
    @IsOpenMap _ _ (curvePlaceSpaceLevelTopology k F S X)
      (curvePlaceSpaceLevelTopology k F S Y) (RingPoints.map f) :=
  curvePlaceSpaceLevel_isOpenMap_of_local k F S hS hX hftX hY hftY f
    (curvePlaceSpaceFactor_isOpenMap_of_smooth k F S hlocal
      hX (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftX)
      hY (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftY) f hf) hs

/-- The same inputs give openness on each actual enlarged curve-place stage. -/
theorem curvePlaceSpaceStage_isOpenMap_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (T : AdelicLevelIndexAbove S)
    (hs : ∀ᶠ i in Filter.cofinite, Function.Surjective
      (RingPoints.map (A := CurvePlaceLevelFactor k F T.val i)
        (curvePlaceSpaceLevelModelMap k F S T f))) :
    @IsOpenMap _ _ (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceStageTopology k F S Y T) (RingPoints.map f) :=
  curvePlaceSpaceStage_isOpenMap_of_local k F S hS hX hftX hY hftY f T
    (curvePlaceSpaceFactor_isOpenMap_of_smooth k F T.val hlocal
      hX.baseChange (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftX).baseChange
      hY.baseChange (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftY).baseChange
      (curvePlaceSpaceLevelModelMap k F S T f) hf.baseChangeMap) hs

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

set_option maxHeartbeats 800000 in
/-- Smooth local openness supplies every number-field factor, including infinite places. -/
theorem numberFieldSpaceFactor_isOpenMap_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u})
    (hX : IsSeparated X) (hlftX : LocallyOfFiniteTypeOverBase X)
    (hY : IsSeparated Y) (hlftY : LocallyOfFiniteTypeOverBase Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (i : NumberFieldLevelFactorIndex K S) :
    @IsOpenMap _ _
      (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K S i))
      (fieldValuedPointTopology _ Y (numberFieldLevelFieldAlgHom K S i))
      (RingPoints.map f) := by
  rcases i with v | v | v
  · let : NontriviallyNormedField (NumberFieldLevelField K S (.inl v)) :=
      AdelicSpaceLocalFields.infiniteNormedField K v
    have : CompleteSpace (NumberFieldLevelField K S (.inl v)) :=
      inferInstanceAs (CompleteSpace (InfiniteCompletion K v))
    let : Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelField K S (.inl v)) :=
      instAdelicSpaceLevelTopology6 K S (.inl v)
    exact isOpenMap_fieldFactor_of_smooth (L := NumberFieldLevelField K S (.inl v))
      hlocal hX hlftX hY hlftY f hf
      (numberFieldLevelFieldAlgHom K S (.inl v)) Function.bijective_id
  · let : NontriviallyNormedField (NumberFieldLevelField K S (.inr (.inl v))) :=
      AdelicSpaceLocalFields.normedField (RingOfIntegers K) K v.1
    have : CompleteSpace (NumberFieldLevelField K S (.inr (.inl v))) :=
      AdelicSpaceLocalFields.completeSpace (RingOfIntegers K) K v.1
    let : Algebra ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelField K S (.inr (.inl v))) :=
      instAdelicSpaceLevelTopology6 K S (.inr (.inl v))
    exact isOpenMap_fieldFactor_of_smooth (L := NumberFieldLevelField K S (.inr (.inl v)))
      hlocal hX hlftX hY hlftY f hf
      (numberFieldLevelFieldAlgHom K S (.inr (.inl v))) Function.bijective_id
  · let : NontriviallyNormedField (NumberFieldLevelField K S (.inr (.inr v))) :=
      AdelicSpaceLocalFields.normedField (RingOfIntegers K) K v.1
    have : CompleteSpace (NumberFieldLevelField K S (.inr (.inr v))) :=
      AdelicSpaceLocalFields.completeSpace (RingOfIntegers K) K v.1
    let O : Subring (NumberFieldLevelField K S (.inr (.inr v))) :=
      (v.1.adicCompletionIntegers K).toSubring
    let : Algebra ((S : Set (FinitePlace K)).integer K) O :=
      instAdelicLevelModelPoints10 K S (.inr (.inr v))
    let : Algebra ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelField K S (.inr (.inr v))) :=
      instAdelicSpaceLevelTopology6 K S (.inr (.inr v))
    have : IsScalarTower ((S : Set (FinitePlace K)).integer K) O
        (NumberFieldLevelField K S (.inr (.inr v))) := ⟨fun c o x => by
      change ((algebraMap _ O c * o : O) : NumberFieldLevelField K S (.inr (.inr v))) * x =
        algebraMap _ (NumberFieldLevelField K S (.inr (.inr v))) c * ((o : _) * x)
      rw [Subring.coe_mul, mul_assoc]
      rfl⟩
    exact isOpenMap_integerFactor_of_smooth O hlocal
      (AdelicSpaceLocalFields.mem_adicCompletionIntegers_iff (RingOfIntegers K) K v.1)
      (AdelicSpaceLocalFields.henselianLocalRing (RingOfIntegers K) K v.1)
      hX hlftX hY hlftY f hf

/-- Smooth local openness and cofinite surjectivity give an open number-field level map. -/
theorem numberFieldSpaceLevel_isOpenMap_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u})
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f)
    (hs : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := NumberFieldLevelFactor K S i) f)) :
    @IsOpenMap _ _ (numberFieldSpaceLevelTopology K S X)
      (numberFieldSpaceLevelTopology K S Y) (RingPoints.map f) :=
  numberFieldSpaceLevel_isOpenMap_of_local K S hX hftX hY hftY f
    (numberFieldSpaceFactor_isOpenMap_of_smooth K S hlocal
      hX (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftX)
      hY (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftY) f hf) hs

/-- The same inputs give openness on each actual enlarged number-field stage. -/
theorem numberFieldSpaceStage_isOpenMap_of_smooth
    (hlocal : CompleteFieldSmoothSpacePointOpenStatement.{u})
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (T : AdelicLevelIndexAbove S)
    (hs : ∀ᶠ i in Filter.cofinite, Function.Surjective
      (RingPoints.map (A := NumberFieldLevelFactor K T.val i)
        (numberFieldSpaceLevelModelMap K S T f))) :
    @IsOpenMap _ _ (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceStageTopology K S Y T) (RingPoints.map f) :=
  numberFieldSpaceStage_isOpenMap_of_local K S hX hftX hY hftY f T
    (numberFieldSpaceFactor_isOpenMap_of_smooth K T.val hlocal
      hX.baseChange (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftX).baseChange
      hY.baseChange (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftY).baseChange
      (numberFieldSpaceLevelModelMap K S T f) hf.baseChangeMap) hs

end NumberField

end Langlands.Global
