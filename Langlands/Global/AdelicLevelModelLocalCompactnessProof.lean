import Langlands.Global.AdelicLevelModelLocalCompactnessStatement
import Langlands.Global.AdelicLevelModelTopologyProof
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.Global.FunctionFieldAdelesLocallyCompactProof
import Langlands.Global.IntegralFiniteAdeles
import Langlands.AlgebraicGeometry.PointTopology.CompactPointProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeLocalCompactnessProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeHausdorffProofs

/-! # Local compactness of actual arithmetic-level model points -/

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

variable [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [T2Space R]

private theorem localModelPoint_locallyCompactSpace
    [IsOpenUnits R] [LocallyCompactSpace R] [LocallyOfFiniteType X.hom] :
    @LocallyCompactSpace (RingPoint R (ringBaseChange C R X) R)
      (schemePointTopology R (ringBaseChange C R X) R) := by
  let := localModel_locallyOfFiniteType C R X
  exact schemePointLocalCompactness_proof R R (ringBaseChange C R X)

private theorem localModelPoint_compactSpace
    [CompactSpace R] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    @CompactSpace (RingPoint R (ringBaseChange C R X) R)
      (schemePointTopology R (ringBaseChange C R X) R) := by
  let := localModel_locallyOfFiniteType C R X
  let := localModel_quasiCompact C R X
  let : CompactSpace (ringBaseChange C R X).left :=
    QuasiCompact.compactSpace_of_compactSpace (ringBaseChange C R X).hom
  exact schemePointCompactness_proof R R (ringBaseChange C R X)

private theorem localModelPoint_t2Space
    [IsOpenUnits R] [IsSeparated X.hom] :
    @T2Space (RingPoint R (ringBaseChange C R X) R)
      (schemePointTopology R (ringBaseChange C R X) R) := by
  let := localModel_isSeparated C R X
  exact t2Space_schemePointTopology R R (ringBaseChange C R X)

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- Finite field factors and compact integer factors give local compactness
without requiring the model to be separated. -/
theorem curvePlaceLevelModelPoint_locallyCompactSpace :
    let := curvePlaceLevelModelPointTopology k F S X
    LocallyCompactSpace
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)) ∧
    (∀ [IsSeparated X.hom],
      T2Space (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))) := by
  let := curvePlaceLevelModelPointTopology k F S X
  let P (i : CurvePlaceLevelFactorIndex k F S) :=
    RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i)
  let : ∀ i, TopologicalSpace (P i) := fun i =>
    schemePointTopology (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i)
  let : ∀ i, IsOpenUnits (CurvePlaceLevelFactor k F S i) :=
    adelicLocalFactorUnits.1 k F S
  let : ∀ i, T2Space (CurvePlaceLevelFactor k F S i) := by
    intro i
    cases i with
    | inl v => exact inferInstanceAs (T2Space (curvePlaceCompletion v.1))
    | inr v => exact inferInstanceAs (T2Space (curvePlaceCompletionIntegers v.1))
  let : ∀ i, LocallyCompactSpace (CurvePlaceLevelFactor k F S i) := by
    intro i
    cases i with
    | inl v => exact curvePlaceCompletion_locallyCompactSpace k F v.1
    | inr v =>
      let := curvePlaceCompletionIntegers_compactSpace k F v.1
      exact inferInstanceAs (LocallyCompactSpace (curvePlaceCompletionIntegers v.1))
  let : ∀ i, LocallyCompactSpace (P i) := fun i =>
    localModelPoint_locallyCompactSpace (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S i) X
  let : ∀ v : {v : AlgebraicCurve.Place k F // v ∉ S},
      CompactSpace (P (.inr v)) := by
    intro v
    let : CompactSpace (CurvePlaceLevelFactor k F S (.inr v)) :=
      curvePlaceCompletionIntegers_compactSpace k F v.1
    exact localModelPoint_compactSpace (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S (.inr v)) X
  let : LocallyCompactSpace (∀ i, P i) :=
    (Homeomorph.sumPiEquivProdPi _ _ P).locallyCompactSpace_iff.mpr inferInstance
  have h := curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType k F S X
  refine ⟨(IsHomeomorph.homeomorph _ h).locallyCompactSpace_iff.mpr inferInstance, ?_⟩
  intro hSeparated
  let : ∀ i, T2Space (P i) := fun i =>
    localModelPoint_t2Space (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S i) X
  exact (IsHomeomorph.homeomorph _ h).isEmbedding.t2Space

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- The compact open completed integer ring is a compact neighborhood of zero. -/
private theorem finiteCompletion_locallyCompactSpace (v : FinitePlace K) :
    LocallyCompactSpace (FiniteCompletion K v) :=
  (isCompact_adicCompletionIntegers K v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers K).zero_mem)

/-- The full number-field level includes all infinite completions. -/
theorem numberFieldLevelModelPoint_locallyCompactSpace :
    let := numberFieldLevelModelPointTopology K S X
    LocallyCompactSpace
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)) ∧
    (∀ [IsSeparated X.hom],
      T2Space
        (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))) := by
  let := numberFieldLevelModelPointTopology K S X
  let P (i : NumberFieldLevelFactorIndex K S) :=
    RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i)
  let : ∀ i, TopologicalSpace (P i) := fun i =>
    schemePointTopology (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i)
  let : ∀ i, IsOpenUnits (NumberFieldLevelFactor K S i) :=
    adelicLocalFactorUnits.2 K S
  let : ∀ i, T2Space (NumberFieldLevelFactor K S i) := by
    intro i
    cases i with
    | inl v => exact inferInstanceAs (T2Space (InfiniteCompletion K v))
    | inr j =>
      cases j with
      | inl v => exact inferInstanceAs (T2Space (FiniteCompletion K v.1))
      | inr v => exact inferInstanceAs (T2Space (v.1.adicCompletionIntegers K))
  let : ∀ i, LocallyCompactSpace (NumberFieldLevelFactor K S i) := by
    intro i
    cases i with
    | inl v => exact inferInstanceAs (LocallyCompactSpace (InfiniteCompletion K v))
    | inr j =>
      cases j with
      | inl v => exact finiteCompletion_locallyCompactSpace K v.1
      | inr v =>
        let : CompactSpace (v.1.adicCompletionIntegers K) :=
          isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers K v.1)
        exact inferInstanceAs (LocallyCompactSpace (v.1.adicCompletionIntegers K))
  let : ∀ i, LocallyCompactSpace (P i) := fun i =>
    localModelPoint_locallyCompactSpace ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S i) X
  let : ∀ v : {v : FinitePlace K // v ∉ S},
      CompactSpace (P (.inr (.inr v))) := by
    intro v
    let : CompactSpace (NumberFieldLevelFactor K S (.inr (.inr v))) :=
      isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers K v.1)
    exact localModelPoint_compactSpace ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S (.inr (.inr v))) X
  let : LocallyCompactSpace (∀ j, P (.inr j)) :=
    (Homeomorph.sumPiEquivProdPi _ _ (fun j => P (.inr j))).locallyCompactSpace_iff.mpr
      inferInstance
  let : LocallyCompactSpace (∀ i, P i) :=
    (Homeomorph.sumPiEquivProdPi _ _ P).locallyCompactSpace_iff.mpr inferInstance
  have h := numberFieldLevelModelPointMap_isHomeomorph_of_finiteType K S X
  refine ⟨(IsHomeomorph.homeomorph _ h).locallyCompactSpace_iff.mpr inferInstance, ?_⟩
  intro hSeparated
  let : ∀ i, T2Space (P i) := fun i =>
    localModelPoint_t2Space ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S i) X
  exact (IsHomeomorph.homeomorph _ h).isEmbedding.t2Space

end NumberField

/-- Corollary 3.7 for the actual arithmetic-level model-point spaces. -/
theorem adelicLevelModelLocalCompactness :
    AdelicLevelModelLocalCompactnessStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S X _ _
    exact curvePlaceLevelModelPoint_locallyCompactSpace k F S X
  · intro K _ _ S X _ _
    exact numberFieldLevelModelPoint_locallyCompactSpace K S X

end Langlands.Global
