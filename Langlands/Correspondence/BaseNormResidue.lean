import Langlands.Correspondence.BaseReciprocityCandidate
import Langlands.ClassFieldTheory.Local.ReciprocitySystemUniquenessProof
import Langlands.ClassFieldTheory.Local.FiniteArtinTransport
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityReconstruction

/-! # The finite norm-residue laws of a supplied common-closure family -/

noncomputable section

universe uF

namespace Langlands.Correspondence

open LocalClassField LocalFactor LocalFactor.CommonClosure Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance baseNormResidueTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance baseNormResidueBottomTopology :
    TopologicalSpace (baseExtension F).field :=
  (fieldData F (baseExtension F)).topology

/-- Finite restriction of the inverse candidate recovers actual Weil projection. -/
theorem finiteRestriction_reciprocityHom (e : ReciprocityCandidate F)
    (L : LocalFiniteAbelianExtension F) (w : localWeilGroup F) :
    finiteFamilyOfHom
        (candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F) e) L
        (reciprocityHom F e w) =
      L.restriction (localProjection F w) := by
  change L.abelianRestriction
      (WeilQuotients.toGroupAbelianization (localResidueDegree F)
        (e.symm (e (WeilQuotients.projection (localResidueDegree F) w)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

/-- The actual norm range over the bottom field transports to the norm range over F. -/
theorem baseFieldUnitsEquiv_mem_normRange_iff
    (M : Extension F) (x : (baseExtension F).fieldˣ) :
    baseFieldUnitsEquiv F x ∈ normSubgroup F.Carrier M.field ↔
      x ∈ ((baseExtension F).unitsNorm M bot_le).range := by
  let : Algebra (baseExtension F).field M.field :=
    (IntermediateField.inclusion (show (baseExtension F).field ≤ M.field from bot_le)).toAlgebra
  let : IsScalarTower F.Carrier (baseExtension F).field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (baseExtension F).field M.field :=
    FiniteDimensional.right F.Carrier (baseExtension F).field M.field
  let eK : (baseExtension F).field ≃+* F.Carrier :=
    (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).toRingEquiv
  have h : (algebraMap F.Carrier M.field).comp eK.toRingHom =
      (RingEquiv.refl M.field).toRingHom.comp
        (algebraMap (baseExtension F).field M.field) := by
    apply RingHom.ext
    intro a
    obtain ⟨b, rfl⟩ :=
      (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm.surjective a
    change algebraMap F.Carrier M.field
        (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)
          ((IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm b)) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl
  exact FiniteArtinTransport.mem_normSubgroup_map_iff eK (RingEquiv.refl M.field) h x

/-- A norm-compatible family has exactly the actual finite norm kernels at the base. -/
theorem finiteNormKernel_baseReciprocityCandidate
    (eC : ReciprocityFamily F)
    (he : LocalClassField.CommonClosure.NormRelation F
      (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F) eC)
    (L : LocalFiniteAbelianExtension F) :
    (finiteFamilyOfHom
      (candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F)
        (baseReciprocityCandidate F eC)) L).toMonoidHom.ker =
      normSubgroup F.Carrier L.field := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let M : Extension F := ⟨L.field.toIntermediateField, inferInstance⟩
  let i : (baseExtension F).field.fixingSubgroup →ₜ*
      Field.absoluteGaloisGroup F.Carrier :=
    ⟨(baseExtension F).field.fixingSubgroup.subtype, continuous_subtype_val⟩
  let H := (abelianizationLift (L.restriction.comp i)).toMonoidHom.ker
  have hM : ∀ s : (baseExtension F).field.fixingSubgroup,
      (QuotientGroup.mk s :
        TopologicalAbelianization (baseExtension F).field.fixingSubgroup) ∈ H ↔
        s.val ∈ M.field.fixingSubgroup := by
    intro s
    change L.restriction s.val = 1 ↔ s.val ∈ M.field.fixingSubgroup
    change s.val ∈ L.restriction.toMonoidHom.ker ↔ _
    rw [show L.restriction.toMonoidHom.ker = M.field.fixingSubgroup from
      L.field.toIntermediateField.restrictNormalHom_ker]
    rfl
  apply Subgroup.ext
  intro x
  obtain ⟨a, rfl⟩ := (baseReciprocityCandidate F eC).surjective x
  induction a using QuotientGroup.induction_on with
  | H w =>
    change finiteFamilyOfHom
        (candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F)
          (baseReciprocityCandidate F eC)) L
        (reciprocityHom F (baseReciprocityCandidate F eC) w) = 1 ↔ _
    rw [finiteRestriction_reciprocityHom]
    have hr := ReciprocitySystemUniqueness.weilGaloisAbelianProjection_mem_iff
      (localResidueDegree F) (baseExtension F) M bot_le H hM
      (QuotientGroup.mk (baseWeilEquiv F w))
    change L.restriction (localProjection F w) = 1 ↔ _ at hr
    have hn := ReciprocitySystemUniqueness.symm_mem_range_iff he
      (baseExtension F) M bot_le
      (reciprocityUnits F eC (baseExtension F) (baseWeilEquiv F w))
    change (eC (baseExtension F)).symm
        (eC (baseExtension F) (QuotientGroup.mk (baseWeilEquiv F w))) ∈ _ ↔ _ at hn
    rw [ContinuousMulEquiv.symm_apply_apply] at hn
    exact (hr.trans hn).trans
      (baseFieldUnitsEquiv_mem_normRange_iff F M
        (reciprocityUnits F eC (baseExtension F) (baseWeilEquiv F w))).symm

/-- Every candidate, independently of norm compatibility, is onto each finite Galois group. -/
theorem finiteRestriction_surjective (e : ReciprocityCandidate F)
    (L : LocalFiniteAbelianExtension F) :
    Function.Surjective (finiteFamilyOfHom
      (candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F) e) L) := by
  intro s
  have hs : Function.Surjective L.restriction := by
    intro t
    exact AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F.Carrier) t
  have hd : DenseRange (fun w : localWeilGroup F =>
      L.restriction (localProjection F w)) :=
    hs.denseRange.comp
      (localProjection_denseRange F) L.restriction.continuous
  obtain ⟨w, hw⟩ := hd.exists_mem_open
    (isOpen_discrete ({s} : Set L.galoisGroup)) (Set.singleton_nonempty s)
  refine ⟨reciprocityHom F e w, ?_⟩
  exact (finiteRestriction_reciprocityHom F e L w).trans hw

/-- The supplied norm-compatible family gives all finite norm-residue laws and density. -/
def BaseProfiniteNormResidueStatement : Prop :=
  ∀ (eC : ReciprocityFamily F),
    LocalClassField.CommonClosure.NormRelation F
      (LocalClassField.CommonClosure.canonicalData F) (localResidueDegree F) eC →
    ProfiniteNormResidueRelation
      (candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F)
        (baseReciprocityCandidate F eC))

theorem baseProfiniteNormResidueProof : BaseProfiniteNormResidueStatement F := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  intro eC he
  refine ⟨FiniteArtinReconstruction.denseRange_of_finite_surjective F.Carrier _
    (finiteRestriction_surjective F (baseReciprocityCandidate F eC)), ?_, ?_⟩
  · intro L
    exact ⟨finiteNormKernel_baseReciprocityCandidate F eC he L,
      finiteRestriction_surjective F (baseReciprocityCandidate F eC) L⟩
  · exact ProfiniteReciprocityReconstruction.finiteFamilyOfHom_compatible F.Carrier _

/-- Normalization additionally gives the existing local candidate relation. -/
theorem localReciprocity_baseReciprocityCandidate
    (eC : ReciprocityFamily F) (he : NormalizedReciprocity F eC) :
    LocalReciprocityCandidateRelation F.canonicalTopologicalData (localResidueDegree F)
      (baseReciprocityCandidate F eC) :=
  ⟨geometricOrder_baseReciprocityCandidate F eC he,
    baseProfiniteNormResidueProof F eC he.1.1⟩

/-- The same local relation holds for every candidate compatible with the family. -/
theorem localReciprocity_of_isBaseReciprocity
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC) (he : NormalizedReciprocity F eC) :
    LocalReciprocityCandidateRelation F.canonicalTopologicalData (localResidueDegree F) e := by
  rw [(isBaseReciprocity_iff_eq_baseReciprocityCandidate F e eC).mp h]
  exact localReciprocity_baseReciprocityCandidate F eC he

end Langlands.Correspondence
