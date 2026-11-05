import Langlands.Global.AdelicLevelModelProperMapStatement
import Langlands.Global.AdelicLevelModelTopologyProof
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.Global.FunctionFieldAdelesLocallyCompactProof
import Langlands.Global.IntegralFiniteAdeles
import Langlands.AlgebraicGeometry.PointTopology.CompactPointProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeHausdorffProofs
import Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointProofs
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # Proper maps on actual arithmetic-level model points: proofs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
variable (X : Over (Spec (CommRingCat.of C)))

private theorem localModel_locallyOfFiniteType [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (ringBaseChange C R X).hom := by
  change LocallyOfFiniteType (pullback.snd X.hom (Spec.algebraMap C R))
  infer_instance

private theorem localModel_quasiCompact [QuasiCompact X.hom] :
    QuasiCompact (ringBaseChange C R X).hom := by
  change QuasiCompact (pullback.snd X.hom (Spec.algebraMap C R))
  infer_instance

private theorem localModel_isSeparated [IsSeparated X.hom] :
    IsSeparated (ringBaseChange C R X).hom := by
  change IsSeparated (pullback.snd X.hom (Spec.algebraMap C R))
  infer_instance

/-- Local field properness applies to the actual base-changed model morphism. -/
private theorem localModelPointMap_isProperMap_of_field
    (C L : Type u) [CommRing C] [Field L] [Algebra C L] [TopologicalSpace L]
    [IsTopologicalDivisionRing L] [T2Space L] [LocallyCompactSpace L]
    (hnondiscrete : ¬ DiscreteTopology L)
    {X Y : Over (Spec (CommRingCat.of C))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    letI : TopologicalSpace (RingPoint L (ringBaseChange C L X) L) :=
      schemePointTopology L (ringBaseChange C L X) L
    letI : TopologicalSpace (RingPoint L (ringBaseChange C L Y) L) :=
      schemePointTopology L (ringBaseChange C L Y) L
    IsProperMap (X := RingPoint L (ringBaseChange C L X) L)
      (Y := RingPoint L (ringBaseChange C L Y) L)
      (fun p : RingPoint L (ringBaseChange C L X) L =>
        (p ≫ (Over.pullback (Spec.algebraMap C L)).map f :
          RingPoint L (ringBaseChange C L Y) L)) := by
  let := localModel_locallyOfFiniteType C L X
  let := localModel_quasiCompact C L X
  let := localModel_isSeparated C L X
  let := localModel_locallyOfFiniteType C L Y
  let := localModel_quasiCompact C L Y
  let := localModel_isSeparated C L Y
  let g : ringBaseChange C L X ⟶ ringBaseChange C L Y :=
    (Over.pullback (Spec.algebraMap C L)).map f
  let : IsProper g.left := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.algebraMap C L) f inferInstance
  exact schemePointLocalProperness_proof L hnondiscrete
    (ringBaseChange C L X) (ringBaseChange C L Y) g

/-- Compact integral source points and Hausdorff target points give properness. -/
private theorem localModelPointMap_isProperMap_of_compact
    (C R : Type u) [CommRing C] [CommRing R] [Algebra C R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [IsOpenUnits R] [T2Space R] [CompactSpace R]
    {X Y : Over (Spec (CommRingCat.of C))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    letI : TopologicalSpace (RingPoint R (ringBaseChange C R X) R) :=
      schemePointTopology R (ringBaseChange C R X) R
    letI : TopologicalSpace (RingPoint R (ringBaseChange C R Y) R) :=
      schemePointTopology R (ringBaseChange C R Y) R
    IsProperMap (X := RingPoint R (ringBaseChange C R X) R)
      (Y := RingPoint R (ringBaseChange C R Y) R)
      (fun p : RingPoint R (ringBaseChange C R X) R =>
        (p ≫ (Over.pullback (Spec.algebraMap C R)).map f :
          RingPoint R (ringBaseChange C R Y) R)) := by
  let := localModel_locallyOfFiniteType C R X
  let := localModel_quasiCompact C R X
  let := localModel_isSeparated C R Y
  let : CompactSpace (ringBaseChange C R X).left :=
    QuasiCompact.compactSpace_of_compactSpace (ringBaseChange C R X).hom
  let : TopologicalSpace (RingPoint R (ringBaseChange C R X) R) :=
    schemePointTopology R (ringBaseChange C R X) R
  let : TopologicalSpace (RingPoint R (ringBaseChange C R Y) R) :=
    schemePointTopology R (ringBaseChange C R Y) R
  let : CompactSpace (RingPoint R (ringBaseChange C R X) R) :=
    schemePointCompactness_proof R R (ringBaseChange C R X)
  let : T2Space (RingPoint R (ringBaseChange C R Y) R) :=
    t2Space_schemePointTopology R R (ringBaseChange C R Y)
  exact (schemePointContinuity_proof R R (ringBaseChange C R X) (ringBaseChange C R Y)
    ((Over.pullback (Spec.algebraMap C R)).map f)).isProperMap

/-- Coefficient restriction and local base change commute with postcomposition. -/
private theorem localModelPointMap_natural
    (C A R : Type u) [CommRing C] [CommRing A] [CommRing R]
    [Algebra C A] [Algebra C R]
    (g : A →ₐ[C] R) {X Y : Over (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) (p : RingPoint C X A) :
    ringPointBaseChangeEquiv C R R Y (RingPoint.changeRing g (p ≫ f)) =
      ringPointBaseChangeEquiv C R R X (RingPoint.changeRing g p) ≫
        (Over.pullback (Spec.algebraMap C R)).map f := by
  rw [show RingPoint.changeRing g (p ≫ f) =
    RingPoint.changeRing g p ≫ f from (Category.assoc _ _ _).symm]
  exact ringPointBaseChangeEquiv_natural C R R f _

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

private theorem nontriviallyNormedField_not_discrete
    (L : Type u) [NontriviallyNormedField L] : ¬ DiscreteTopology L := by
  intro h
  let := h
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm L
  exact (not_lt_of_ge (NormedDivisionRing.norm_le_one_of_discrete x)) hx

private theorem curvePlaceCompletion_not_discrete
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    (v : AlgebraicCurve.Place k F) : ¬ DiscreteTopology (curvePlaceCompletion v) := by
  let : (Valued.v : Valuation (curvePlaceCompletion v)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let : NontriviallyNormedField (curvePlaceCompletion v) :=
    Valued.toNontriviallyNormedField (curvePlaceCompletion v) (WithZero (Multiplicative ℤ))
  exact nontriviallyNormedField_not_discrete (curvePlaceCompletion v)

private theorem finiteCompletion_not_discrete
    (K : Type u) [Field K] [NumberField K] (v : FinitePlace K) :
    ¬ DiscreteTopology (FiniteCompletion K v) := by
  let : NontriviallyNormedField (FiniteCompletion K v) :=
    Valued.toNontriviallyNormedField (FiniteCompletion K v) (WithZero (Multiplicative ℤ))
  exact nontriviallyNormedField_not_discrete (FiniteCompletion K v)

private theorem infiniteCompletion_not_discrete
    (K : Type u) [Field K] (v : InfinitePlace K) :
    ¬ DiscreteTopology (InfiniteCompletion K v) := by
  intro hdiscrete
  let := hdiscrete
  have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
    (map_zero (NumberField.InfinitePlace.Completion.extensionEmbedding v)) (2 : v.Completion)
  have hnorm : 1 < ‖(2 : v.Completion)‖ := by
    rw [← h]
    norm_num only [map_ofNat, Complex.norm_ofNat]
  exact (not_lt_of_ge (NormedDivisionRing.norm_le_one_of_discrete (2 : v.Completion))) hnorm

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable {X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
variable [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
variable (f : X ⟶ Y) [IsProper f.left]

/-- Proper model morphisms induce proper maps on actual curve-place level points. -/
theorem curvePlaceLevelModelPointMap_isProperMap :
    letI : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S X
    letI : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) Y
      (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S Y
    IsProperMap
      (X := RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (Y := RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))) := by
  let : LocallyOfFiniteType X.hom := by
    rw [← Over.w f]
    infer_instance
  let : QuasiCompact X.hom := by
    rw [← Over.w f]
    infer_instance
  let : IsSeparated X.hom := by
    rw [← Over.w f]
    infer_instance
  let : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S X
  let : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) Y
      (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S Y
  let (i : CurvePlaceLevelFactorIndex k F S) : TopologicalSpace
      (RingPoint (CurvePlaceLevelFactor k F S i)
        (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
        (CurvePlaceLevelFactor k F S i)) := schemePointTopology _ _ _
  let (i : CurvePlaceLevelFactorIndex k F S) : TopologicalSpace
      (RingPoint (CurvePlaceLevelFactor k F S i)
        (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) Y)
        (CurvePlaceLevelFactor k F S i)) := schemePointTopology _ _ _
  let (i : CurvePlaceLevelFactorIndex k F S) : IsOpenUnits (CurvePlaceLevelFactor k F S i) :=
    adelicLocalFactorUnits.1 k F S i
  let (i : CurvePlaceLevelFactorIndex k F S) : T2Space (CurvePlaceLevelFactor k F S i) := by
    cases i with
    | inl v => exact inferInstanceAs (T2Space (curvePlaceCompletion v.1))
    | inr v => exact inferInstanceAs (T2Space (curvePlaceCompletionIntegers v.1))
  have hX := curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType k F S X
  have hY := curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType k F S Y
  have hfactor : ∀ i : CurvePlaceLevelFactorIndex k F S,
      IsProperMap
        (X := RingPoint (CurvePlaceLevelFactor k F S i)
          (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
          (CurvePlaceLevelFactor k F S i))
        (Y := RingPoint (CurvePlaceLevelFactor k F S i)
          (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) Y)
          (CurvePlaceLevelFactor k F S i))
        (fun p => (p ≫ (Over.pullback
          (Spec.algebraMap (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i))).map f)) := by
    intro i
    cases i with
    | inl v =>
      let : LocallyCompactSpace (curvePlaceCompletion v.1) :=
        curvePlaceCompletion_locallyCompactSpace k F v.1
      exact localModelPointMap_isProperMap_of_field (curvePlaceSIntegers k F S)
        (curvePlaceCompletion v.1) (curvePlaceCompletion_not_discrete k F v.1) f
    | inr v =>
      let : CompactSpace (CurvePlaceLevelFactor k F S (.inr v)) :=
        curvePlaceCompletionIntegers_compactSpace k F v.1
      exact localModelPointMap_isProperMap_of_compact (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F S (.inr v)) f
  have hlocal := IsProperMap.pi_map
    (X := fun i => RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i))
    (Y := fun i => RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) Y)
      (CurvePlaceLevelFactor k F S i)) hfactor
  have hcomp : IsProperMap ((curvePlaceLevelModelPointMap k F S Y) ∘
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S)))) := by
    convert hlocal.comp hX.isProperMap using 1
    funext p i
    exact localModelPointMap_natural (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S)
      (CurvePlaceLevelFactor k F S i) (curvePlaceLevelFactorAlgHom k F S i) f p
  exact isProperMap_of_comp_of_inj
    (hY.isInducing.continuous_iff.mpr hcomp.continuous) hY.continuous hcomp hY.injective

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable {X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
variable [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
variable (f : X ⟶ Y) [IsProper f.left]

/-- Proper model morphisms induce proper maps on the full number-field level points. -/
theorem numberFieldLevelModelPointMap_isProperMap :
    letI : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S X
    letI : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) Y
      (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S Y
    IsProperMap
      (X := RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (Y := RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))) := by
  let : LocallyOfFiniteType X.hom := by
    rw [← Over.w f]
    infer_instance
  let : QuasiCompact X.hom := by
    rw [← Over.w f]
    infer_instance
  let : IsSeparated X.hom := by
    rw [← Over.w f]
    infer_instance
  let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S X
  let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) Y
      (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S Y
  let (i : NumberFieldLevelFactorIndex K S) : TopologicalSpace
      (RingPoint (NumberFieldLevelFactor K S i)
        (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
        (NumberFieldLevelFactor K S i)) := schemePointTopology _ _ _
  let (i : NumberFieldLevelFactorIndex K S) : TopologicalSpace
      (RingPoint (NumberFieldLevelFactor K S i)
        (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) Y)
        (NumberFieldLevelFactor K S i)) := schemePointTopology _ _ _
  let (i : NumberFieldLevelFactorIndex K S) : IsOpenUnits (NumberFieldLevelFactor K S i) :=
    adelicLocalFactorUnits.2 K S i
  let (i : NumberFieldLevelFactorIndex K S) : T2Space (NumberFieldLevelFactor K S i) := by
    cases i with
    | inl v => exact inferInstanceAs (T2Space (InfiniteCompletion K v))
    | inr j =>
      cases j with
      | inl v => exact inferInstanceAs (T2Space (FiniteCompletion K v.1))
      | inr v => exact inferInstanceAs (T2Space (v.1.adicCompletionIntegers K))
  have hX := numberFieldLevelModelPointMap_isHomeomorph_of_finiteType K S X
  have hY := numberFieldLevelModelPointMap_isHomeomorph_of_finiteType K S Y
  have hfactor : ∀ i : NumberFieldLevelFactorIndex K S,
      IsProperMap
        (X := RingPoint (NumberFieldLevelFactor K S i)
          (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
          (NumberFieldLevelFactor K S i))
        (Y := RingPoint (NumberFieldLevelFactor K S i)
          (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) Y)
          (NumberFieldLevelFactor K S i))
        (fun p => (p ≫ (Over.pullback
          (Spec.algebraMap ((S : Set (FinitePlace K)).integer K)
            (NumberFieldLevelFactor K S i))).map f)) := by
    intro i
    cases i with
    | inl v =>
      exact localModelPointMap_isProperMap_of_field ((S : Set (FinitePlace K)).integer K)
        (InfiniteCompletion K v) (infiniteCompletion_not_discrete K v) f
    | inr j =>
      cases j with
      | inl v =>
        let : LocallyCompactSpace (FiniteCompletion K v.1) :=
          (isCompact_adicCompletionIntegers K v.1).locallyCompactSpace_of_mem_nhds_of_addGroup
            ((Valued.isOpen_valuationSubring _).mem_nhds (v.1.adicCompletionIntegers K).zero_mem)
        exact localModelPointMap_isProperMap_of_field ((S : Set (FinitePlace K)).integer K)
          (FiniteCompletion K v.1) (finiteCompletion_not_discrete K v.1) f
      | inr v =>
        let : CompactSpace (NumberFieldLevelFactor K S (.inr (.inr v))) :=
          isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers K v.1)
        exact localModelPointMap_isProperMap_of_compact ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K S (.inr (.inr v))) f
  have hlocal := IsProperMap.pi_map
    (X := fun i => RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i))
    (Y := fun i => RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) Y)
      (NumberFieldLevelFactor K S i)) hfactor
  have hcomp : IsProperMap ((numberFieldLevelModelPointMap K S Y) ∘
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S)))) := by
    convert hlocal.comp hX.isProperMap using 1
    funext p i
    exact localModelPointMap_natural ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S)
      (NumberFieldLevelFactor K S i) (numberFieldLevelFactorAlgHom K S i) f p
  exact isProperMap_of_comp_of_inj
    (hY.isInducing.continuous_iff.mpr hcomp.continuous) hY.continuous hcomp hY.injective

end NumberField

/-- The exact arithmetic-level proper-map statement in both global-field cases. -/
theorem adelicLevelModelProperMap : AdelicLevelModelProperMapStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S X Y _ _ _ f _
    exact curvePlaceLevelModelPointMap_isProperMap k F S f
  · intro K _ _ S X Y _ _ _ f _
    exact numberFieldLevelModelPointMap_isProperMap K S f

end Langlands.Global
