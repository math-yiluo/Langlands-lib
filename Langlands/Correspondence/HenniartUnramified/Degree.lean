import Langlands.Correspondence.HenniartWeilElementaryLayer
import Langlands.ClassFieldTheory.Local.ReciprocitySystemUniquenessProof
import Langlands.Galois.Local.TotallyRamifiedSolvabilityProof
import Langlands.Galois.Local.UnramifiedCriterionProof
import Langlands.LocalFactor.Ramification.Herbrand.WeilRestrictionProof
import Langlands.LocalFactor.Ramification.Herbrand.SlopeProof
import Langlands.Weil.Local.DegreeFrobenius

/-! # Unramified fields and degree-divisible Weil subgroups -/

noncomputable section

namespace Langlands.Henniart.Numerical

open LocalClassField LocalClassField.ReciprocitySystemUniqueness Weil.Local

universe uK

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- The degree-modulo-`i` map on the actual absolute Galois group. -/
private def galoisMod (i : ℕ) [NeZero i] :
    Field.absoluteGaloisGroup K.Carrier →ₜ* Multiplicative (ZMod i) :=
  (profiniteIntegerMod i).comp (localResidueDegree K)

private theorem galoisMod_localProjection (i : ℕ) [NeZero i] (w : localWeilGroup K) :
    galoisMod K i (localProjection K w) = Multiplicative.ofAdd (localDegreeInt K w : ZMod i) := by
  change profiniteIntegerMod i (localResidueDegree K (localProjection K w)) = _
  rw [show localResidueDegree K (localProjection K w) = Weil.frobenius (localDegree K w)
    from w.property, profiniteIntegerMod_frobenius]
  rfl

private theorem galoisMod_surjective (i : ℕ) [NeZero i] :
    Function.Surjective (galoisMod K i) := by
  intro x
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective x.toAdd
  obtain ⟨w, hw⟩ := localDegree_surjective K (Multiplicative.ofAdd n)
  exact ⟨localProjection K w, by
    rw [galoisMod_localProjection, localDegreeInt, hw]
    exact congrArg Multiplicative.ofAdd hn⟩

local instance : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier

/-- The fixed field of the degree-modulo-`i` kernel, inside the fixed algebraic closure. -/
def unramifiedStage (i : ℕ) [NeZero i] : FiniteIntermediateExtension K.Carrier := by
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  let H := (galoisMod K i).toMonoidHom.ker
  have hker : (H : Set (Field.absoluteGaloisGroup K.Carrier)) =
      (galoisMod K i) ⁻¹' {1} := rfl
  have hopen : IsOpen (H : Set (Field.absoluteGaloisGroup K.Carrier)) := by
    rw [hker]
    exact (isOpen_discrete _).preimage (galoisMod K i).continuous
  have hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup K.Carrier)) := by
    rw [hker]
    exact isClosed_singleton.preimage (galoisMod K i).continuous
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hclosed⟩
  refine ⟨IntermediateField.fixedField H, (InfiniteGalois.isOpen_iff_finite _).mp ?_⟩
  rw [hfix]
  exact hopen

private theorem unramifiedStage_fixingSubgroup (i : ℕ) [NeZero i] :
    (unramifiedStage K i).field.fixingSubgroup = (galoisMod K i).toMonoidHom.ker := by
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  change (IntermediateField.fixedField (galoisMod K i).toMonoidHom.ker).fixingSubgroup = _
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨_, isClosed_singleton.preimage (galoisMod K i).continuous⟩

instance unramifiedStage_isGalois (i : ℕ) [NeZero i] :
    IsGalois K.Carrier (unramifiedStage K i).field := by
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  apply (InfiniteGalois.normal_iff_isGalois _).mp
  rw [unramifiedStage_fixingSubgroup]
  exact (galoisMod K i).toMonoidHom.normal_ker

/-- Absolute inertia fixes the stage of every positive degree. -/
theorem unramifiedStage_inertia_le (i : ℕ) [NeZero i] :
    K.absoluteInertia K.canonicalTopologicalData ≤ (unramifiedStage K i).field.fixingSubgroup := by
  intro σ hσ
  rw [unramifiedStage_fixingSubgroup, MonoidHom.mem_ker]
  rw [← localResidueDegree_ker, MonoidHom.mem_ker] at hσ
  change localResidueDegree K σ = 1 at hσ
  change profiniteIntegerMod i (localResidueDegree K σ) = 1
  rw [hσ, map_one]

private theorem unramifiedStage_finrank (i : ℕ) [NeZero i] :
    Module.finrank K.Carrier (unramifiedStage K i).field = i := by
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, unramifiedStage_fixingSubgroup]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (galoisMod_surjective K i)).toEquiv).trans (by simp)

/-- The prescribed field is an unramified extension of degree `i` in the target's sense. -/
theorem unramifiedStage_isUnramifiedOfDegree (i : ℕ) [NeZero i] :
    IsUnramifiedOfDegree K ((unramifiedStage K i).asPadicField (p := p))
      (intermediateEmbedding K (unramifiedStage K i)) i := by
  let E := unramifiedStage K i
  have hdeg : extensionDegree K (E.asPadicField (p := p)) (intermediateEmbedding K E) = i :=
    (PadicField.extensionDegree_intermediateEmbedding K E).trans (unramifiedStage_finrank K i)
  have hin := (PadicField.absoluteInertia_le_fixingSubgroup_iff K E).mp
    (unramifiedStage_inertia_le K i)
  exact ⟨hdeg, ((PadicField.absoluteInertia_le_extensionGaloisMap_range_iff K _ _).mp hin).trans hdeg⟩

/-- Its residue cardinality is the `i`th power of the base residue cardinality. -/
theorem unramifiedStage_residueCardinality (i : ℕ) [NeZero i] :
    ((unramifiedStage K i).asPadicField (p := p)).canonicalTopologicalData.residueCardinality =
      K.canonicalTopologicalData.residueCardinality ^ i := by
  rw [extensionResidueCardinality K _ (intermediateEmbedding K (unramifiedStage K i)),
    (unramifiedStage_isUnramifiedOfDegree K i).2]

/-- Membership in the actual Weil subgroup is exactly divisibility of geometric degree. -/
theorem mem_unramifiedStage_weilRange (i : ℕ) [NeZero i] (w : localWeilGroup K) :
    w ∈ (intermediateWeilMap K (unramifiedStage K i)).toMonoidHom.range ↔
      (i : ℤ) ∣ localDegreeInt K w := by
  rw [intermediateWeilMap_range]
  change localProjection K w ∈ (unramifiedStage K i).field.fixingSubgroup ↔ _
  rw [unramifiedStage_fixingSubgroup]
  change galoisMod K i (localProjection K w) = 1 ↔ _
  rw [galoisMod_localProjection]
  change Multiplicative.ofAdd (localDegreeInt K w : ZMod i) = Multiplicative.ofAdd 0 ↔ _
  exact Multiplicative.ofAdd.injective.eq_iff.trans (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)

/-- The actual intermediate Weil embedding is an open topological embedding. -/
theorem unramifiedStage_weilMap_isOpenEmbedding (i : ℕ) [NeZero i] :
    Topology.IsOpenEmbedding (intermediateWeilMap K (unramifiedStage K i)) := by
  refine ⟨intermediateWeilMap_isEmbedding K _, ?_⟩
  have h : Set.range (intermediateWeilMap K (unramifiedStage K i)) =
      (fun w => galoisMod K i (localProjection K w)) ⁻¹' {1} := by
    ext w
    change w ∈ (intermediateWeilMap K (unramifiedStage K i)).toMonoidHom.range ↔ _
    rw [intermediateWeilMap_range]
    change localProjection K w ∈ (unramifiedStage K i).field.fixingSubgroup ↔ _
    rw [unramifiedStage_fixingSubgroup]
    exact Iff.rfl
  rw [h]
  exact (isOpen_discrete _).preimage ((galoisMod K i).continuous.comp (localProjection K).continuous)

/-- The Weil image contains all inertia, not just its intersection with the image. -/
theorem unramifiedStage_localInertia_le (i : ℕ) [NeZero i] :
    localInertia K ≤ (intermediateWeilMap K (unramifiedStage K i)).toMonoidHom.range := by
  intro w hw
  apply (mem_unramifiedStage_weilRange K i w).mpr
  change localDegree K w = 1 at hw
  rw [localDegreeInt, hw]
  exact dvd_zero _

open Ramification.HerbrandBridge Ramification.Padic in
/-- The relative inverse Herbrand function of an unramified stage fixes nonnegative indices. -/
theorem unramifiedStage_herbrandPsi (i : ℕ) [NeZero i] {v : ℝ} (hv : 0 ≤ v) :
    relativeHerbrandPsi (F := K) (unramifiedStage K i) v = v := by
  let E := unramifiedStage K i
  have h0 : absoluteUpperRamificationGroup K 0 ≤ E.field.fixingSubgroup := by
    rw [absoluteUpperCanonicalInertia]
    exact unramifiedStage_inertia_le K i
  have hidx : E.field.fixingSubgroup.relIndex
      (K.absoluteInertia K.canonicalTopologicalData) = 1 :=
    Subgroup.relIndex_eq_one.mpr (unramifiedStage_inertia_le K i)
  have h := relativeHerbrandPsi_sub_eq_relIndex E (le_refl (0 : ℝ)) h0 (le_refl 0) hv
  rw [relativeHerbrandPsi_zero, sub_zero, sub_zero, hidx, Nat.cast_one, one_mul] at h
  exact h

open Ramification.HerbrandBridge VirtualRepresentation.LocalWeil.Ramification in
/-- Under the embedding, a nonnegative upper group pulls back to the same index. -/
theorem unramifiedStage_mem_upperGroup (i : ℕ) [NeZero i] {v : ℝ} (hv : 0 ≤ v)
    (w : localWeilGroup ((unramifiedStage K i).asPadicField (p := p))) :
    intermediateWeilMap K (unramifiedStage K i) w ∈ upperGroup K v ↔ w ∈ upperGroup _ v := by
  rw [intermediateWeilMap_mem_upperGroup_iff _ ((by norm_num : (-1 : ℝ) ≤ 0).trans hv),
    unramifiedStage_herbrandPsi K i hv]

open Ramification.HerbrandBridge Ramification.Padic VirtualRepresentation.LocalWeil.Ramification in
/-- Every element of a nonnegative upper group has a preimage in the stage. -/
theorem unramifiedStage_upperGroup_le (i : ℕ) [NeZero i] {v : ℝ} (hv : 0 ≤ v) :
    upperGroup K v ≤ (intermediateWeilMap K (unramifiedStage K i)).toMonoidHom.range := by
  apply le_trans _ (unramifiedStage_localInertia_le K i)
  intro w hw
  rw [localInertia_eq_comap, Subgroup.mem_comap, ← absoluteUpperCanonicalInertia]
  exact absoluteUpperRamificationGroup_antitone K hv hw

end Langlands.Henniart.Numerical
