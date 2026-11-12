import Langlands.Global.AdelicSpaceCoordinateProperReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeBaseChangeStatement

/-! # Local-to-stage properness for adelic points of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

namespace AdelicSpaceProperReduction

variable {C : Type u} [CommRing C]
  {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}
  {L : Type u} [NontriviallyNormedField L] [LocallyCompactSpace L] [Algebra C L]

/-- The local proper-point theorem applies to a proper model's generic fibre. -/
theorem isProperMap_genericFiber
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u})
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing C X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing C Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) :
    @IsProperMap _ _
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) Y))
      (RingPoints.map (baseChangeMap (Spec.algebraMap C L) f)) :=
  hlocal L _ _ _ (SpaceProductPoints.isQuasiSeparated_of_isSeparated hX).baseChange
    (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftX).baseChange
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hY).baseChange
    (AdelicSpaceLevelFactors.locallyOfFiniteTypeOverBase hftY).baseChange
    (hbc _ _ _ _ _ _ hf)

end AdelicSpaceProperReduction

open AdelicSpaceProperReduction
open AdelicSpaceLocalFields

set_option backward.isDefEq.respectTransparency false

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- Every curve-place factor map is proper, conditional on the local geometric inputs. -/
theorem curvePlaceSpaceFactor_isProperMap_of_proper
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u})
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) (i : CurvePlaceLevelFactorIndex k F S) :
    @IsProperMap _ _
      (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F S i))
      (fieldValuedPointTopology _ Y (curvePlaceLevelFieldAlgHom k F S i))
      (RingPoints.map f) := by
  rcases i with v | v
  · let : NontriviallyNormedField (CurvePlaceLevelField k F S (.inl v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have : LocallyCompactSpace (CurvePlaceLevelField k F S (.inl v)) :=
      curvePlaceCompletion_locallyCompactSpace k F v.1
    let : Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F S (.inl v)) :=
      instAdelicSpaceLevelTopology3 k F S (.inl v)
    exact isProperMap_fieldFactor f (curvePlaceLevelFieldAlgHom k F S (.inl v))
      Function.bijective_id
      (isProperMap_genericFiber hlocal hbc hX hftX hY hftY f hf)
  · let : NontriviallyNormedField (CurvePlaceLevelField k F S (.inr v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    let : Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F S (.inr v)) :=
      instAdelicSpaceLevelTopology3 k F S (.inr v)
    exact isProperMap_compactFactor (L := CurvePlaceLevelField k F S (.inr v))
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum)
      hY hftY f (curvePlaceLevelFieldAlgHom k F S (.inr v))
      (AdelicSpaceLevelTopologyProof.curve_integer k F S hX hftX v).1
      (AdelicSpaceLevelTopologyProof.curve_factor k F S hY hftY (.inr v)).1

/-- Properness of every coordinate gives properness on an actual curve-place level. -/
theorem curvePlaceSpaceLevel_isProperMap_of_proper
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) :
    @IsProperMap _ _ (curvePlaceSpaceLevelTopology k F S X)
      (curvePlaceSpaceLevelTopology k F S Y) (RingPoints.map f) :=
  isProperMap_coordinatePointMap_of_local
    (CurvePlaceLevelFactor k F S) (CurvePlaceLevelField k F S)
    (curvePlaceLevelFieldAlgHom k F S) (curvePlaceLevelFactorAlgHom k F S) f
    (curvePlaceSpaceLevelPoints k F S hS X hX hftX)
    (curvePlaceSpaceLevelPoints k F S hS Y hY hftY)
    (curvePlaceSpaceFactor_isProperMap_of_proper k F S hlocal hbc hX hftX hY hftY f hf)

/-- Properness at the enlarged model level transfers to every curve-place stage. -/
theorem curvePlaceSpaceStage_isProperMap_of_proper
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) (T : AdelicLevelIndexAbove S) :
    @IsProperMap _ _ (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceStageTopology k F S Y T) (RingPoints.map f) := by
  let := curvePlaceSpaceStageTopology k F S X T
  let := curvePlaceSpaceStageTopology k F S Y T
  let := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X)
  let := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property Y)
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact isProperMap_of_homeomorph
    (curvePlaceSpaceStagePointHomeomorph k F S X T)
    (curvePlaceSpaceStagePointHomeomorph k F S Y T) _ _
    (curvePlaceSpaceLevel_isProperMap_of_proper k F T.val hlocal hbc
      (Finset.Nonempty.mono T.property hS)
      hX.baseChange hftX.baseChange hY.baseChange hftY.baseChange
      (curvePlaceSpaceLevelModelMap k F S T f) (hbc _ _ _ _ _ _ hf))
    (curvePlaceSpaceStageEquiv_map k F S T f)

/-- The actual curve-place stage map, bundled with continuity and properness. -/
def curvePlaceSpaceStageProperMap
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) (T : AdelicLevelIndexAbove S) :
    {g : @ContinuousMap
      (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
      (RingPoints (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T))
      (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceStageTopology k F S Y T) //
      @IsProperMap _ _ (curvePlaceSpaceStageTopology k F S X T)
        (curvePlaceSpaceStageTopology k F S Y T) g} :=
  letI := curvePlaceSpaceStageTopology k F S X T
  letI := curvePlaceSpaceStageTopology k F S Y T
  let hp := curvePlaceSpaceStage_isProperMap_of_proper k F S
    hlocal hbc hS hX hftX hY hftY f hf T
  ⟨⟨RingPoints.map f, hp.continuous⟩, hp⟩

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

set_option maxHeartbeats 800000 in
/-- Every number-field factor map is proper, including every infinite-place factor. -/
theorem numberFieldSpaceFactor_isProperMap_of_proper
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u})
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) (i : NumberFieldLevelFactorIndex K S) :
    @IsProperMap _ _
      (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K S i))
      (fieldValuedPointTopology _ Y (numberFieldLevelFieldAlgHom K S i))
      (RingPoints.map f) := by
  rcases i with v | v | v
  · let : NontriviallyNormedField (NumberFieldLevelField K S (.inl v)) :=
      infiniteNormedField K v
    have : LocallyCompactSpace (NumberFieldLevelField K S (.inl v)) :=
      inferInstanceAs (LocallyCompactSpace (InfiniteCompletion K v))
    let : Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelField K S (.inl v)) :=
      instAdelicSpaceLevelTopology6 K S (.inl v)
    exact isProperMap_fieldFactor f (numberFieldLevelFieldAlgHom K S (.inl v))
      Function.bijective_id
      (isProperMap_genericFiber hlocal hbc hX hftX hY hftY f hf)
  · let : NontriviallyNormedField (NumberFieldLevelField K S (.inr (.inl v))) :=
      normedField (NumberField.RingOfIntegers K) K v.1
    have : LocallyCompactSpace (NumberFieldLevelField K S (.inr (.inl v))) :=
      AdelicSpaceLevelTopologyProof.finiteCompletion_locallyCompactSpace K v.1
    let : Algebra ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelField K S (.inr (.inl v))) :=
      instAdelicSpaceLevelTopology6 K S (.inr (.inl v))
    exact isProperMap_fieldFactor f (numberFieldLevelFieldAlgHom K S (.inr (.inl v)))
      Function.bijective_id
      (isProperMap_genericFiber hlocal hbc hX hftX hY hftY f hf)
  · let : NontriviallyNormedField (NumberFieldLevelField K S (.inr (.inr v))) :=
      normedField (NumberField.RingOfIntegers K) K v.1
    let : Algebra ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelField K S (.inr (.inr v))) :=
      instAdelicSpaceLevelTopology6 K S (.inr (.inr v))
    exact isProperMap_compactFactor (L := NumberFieldLevelField K S (.inr (.inr v)))
      (isHenselianValuedField (NumberField.RingOfIntegers K) K v.1)
      hY hftY f (numberFieldLevelFieldAlgHom K S (.inr (.inr v)))
      (AdelicSpaceLevelTopologyProof.numberField_integer K S hX hftX v).1
      (AdelicSpaceLevelTopologyProof.numberField_factor K S hY hftY (.inr (.inr v))).1

/-- Properness of every coordinate gives properness on a number-field level. -/
theorem numberFieldSpaceLevel_isProperMap_of_proper
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u})
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) :
    @IsProperMap _ _ (numberFieldSpaceLevelTopology K S X)
      (numberFieldSpaceLevelTopology K S Y) (RingPoints.map f) :=
  isProperMap_coordinatePointMap_of_local
    (NumberFieldLevelFactor K S) (NumberFieldLevelField K S)
    (numberFieldLevelFieldAlgHom K S) (numberFieldLevelFactorAlgHom K S) f
    (numberFieldSpaceLevelPoints K S X hX hftX)
    (numberFieldSpaceLevelPoints K S Y hY hftY)
    (numberFieldSpaceFactor_isProperMap_of_proper K S hlocal hbc hX hftX hY hftY f hf)

/-- Properness at the enlarged model level transfers to every number-field stage. -/
theorem numberFieldSpaceStage_isProperMap_of_proper
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u})
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) (T : AdelicLevelIndexAbove S) :
    @IsProperMap _ _ (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceStageTopology K S Y T) (RingPoints.map f) := by
  let := numberFieldSpaceStageTopology K S X T
  let := numberFieldSpaceStageTopology K S Y T
  let := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X)
  let := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property Y)
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact isProperMap_of_homeomorph
    (numberFieldSpaceStagePointHomeomorph K S X T)
    (numberFieldSpaceStagePointHomeomorph K S Y T) _ _
    (numberFieldSpaceLevel_isProperMap_of_proper K T.val hlocal hbc
      hX.baseChange hftX.baseChange hY.baseChange hftY.baseChange
      (numberFieldSpaceLevelModelMap K S T f) (hbc _ _ _ _ _ _ hf))
    (numberFieldSpaceStageEquiv_map K S T f)

/-- The actual number-field stage map, bundled with continuity and properness. -/
def numberFieldSpaceStageProperMap
    (hlocal : LocalFieldProperPointMapStatement.{u})
    (hbc : ProperSchemeBaseChangeStatement.{u})
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsProperMorphism f) (T : AdelicLevelIndexAbove S) :
    {g : @ContinuousMap
      (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
      (RingPoints ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevelOver K S T))
      (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceStageTopology K S Y T) //
      @IsProperMap _ _ (numberFieldSpaceStageTopology K S X T)
        (numberFieldSpaceStageTopology K S Y T) g} :=
  letI := numberFieldSpaceStageTopology K S X T
  letI := numberFieldSpaceStageTopology K S Y T
  let hp := numberFieldSpaceStage_isProperMap_of_proper K S
    hlocal hbc hX hftX hY hftY f hf T
  ⟨⟨RingPoints.map f, hp.continuous⟩, hp⟩

end NumberField

end Langlands.Global
