import Langlands.ClassFieldTheory.Local.IntermediateReciprocityTransport
import Langlands.ClassFieldTheory.Local.DenseTransferNaturality
import Langlands.ClassFieldTheory.Local.CommonClosureReciprocityConstruction

/-! # Transfer transport from fixing Galois subgroups to actual common-closure Weil groups -/

noncomputable section

namespace Langlands.LocalClassField

open Weil Weil.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance transferBaseCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

namespace CommonClosure

/-- The actual Weil projection has dense image in each literal fixing subgroup. -/
theorem fixingWeilProjection_denseRange (E : FiniteIntermediateExtension F.Carrier) :
    DenseRange (E.weilGaloisProjection (localResidueDegree F)) := by
  let j := intermediateWeilEquiv F E
  let g := intermediateGaloisEquiv F E
  have hd := g.surjective.denseRange.comp
    (localProjection_denseRange (E.asPadicField (p := p))) g.continuous
  have hd' := hd.comp j.symm.surjective.denseRange
    (g.continuous.comp (localProjection (E.asPadicField (p := p))).continuous)
  have hfunc : (fun x => g (localProjection (E.asPadicField (p := p)) (j.symm x))) =
      E.weilGaloisProjection (localResidueDegree F) := by
    funext x
    have h := intermediateGaloisEquiv_projection F E (j.symm x)
    change g (localProjection (E.asPadicField (p := p)) (j.symm x)) =
      E.weilGaloisProjection (localResidueDegree F) (j (j.symm x)) at h
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h
  rw [← hfunc]
  exact hd'

/-- The actual Weil and Galois finite-coset transfers commute with projection. -/
theorem weilGaloisAbelianProjection_transfer
    (E L : FiniteIntermediateExtension F.Carrier) (h : E.field ≤ L.field) :
    (L.weilGaloisAbelianProjection (localResidueDegree F)).comp
      (E.weilAbelianTransfer L h (localResidueDegree F)) =
    (E.galoisAbelianTransfer L h).comp
      (E.weilGaloisAbelianProjection (localResidueDegree F)) := by
  let hG := IntermediateField.fixingSubgroup_antitone h
  let hW := Subgroup.comap_mono
    (f := (Weil.projection (localResidueDegree F)).toMonoidHom) hG
  let HG := L.field.fixingSubgroup.subgroupOf E.field.fixingSubgroup
  let HW := (pullbackFixingSubgroup F.Carrier L.field (localResidueDegree F)).subgroupOf
    (pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F))
  let f := E.weilGaloisProjection (localResidueDegree F)
  have hHG : IsOpen (HG : Set E.field.fixingSubgroup) :=
    L.field.fixingSubgroup_isOpen.preimage continuous_subtype_val
  let := absoluteFixingFiniteIndex F.Carrier L.field
  let := pullbackFixingFiniteIndex F.Carrier L.field (localResidueDegree F)
  have ht := TransferNaturality.abelianizedTransfer_naturality f HG
    (fixingWeilProjection_denseRange F E) hHG
  let eW : HW ≃ₜ* pullbackFixingSubgroup F.Carrier L.field (localResidueDegree F) :=
    subgroupOfEquiv hW
  let eG : HG ≃ₜ* L.field.fixingSubgroup := subgroupOfEquiv hG
  have heq :
      (abelianizationMap (L.weilGaloisProjection (localResidueDegree F))).comp
        (abelianizationMap (eW : HW →ₜ* pullbackFixingSubgroup F.Carrier L.field (localResidueDegree F))) =
      (abelianizationMap (eG : HG →ₜ* L.field.fixingSubgroup)).comp
        (abelianizationMap (TransferNaturality.subgroupPreimageMap f HG)) := by
    rw [← abelianizationMap_comp, ← abelianizationMap_comp]
    rfl
  calc
    _ = ((abelianizationMap (L.weilGaloisProjection (localResidueDegree F))).comp
        (abelianizationMap (eW : HW →ₜ* pullbackFixingSubgroup F.Carrier L.field (localResidueDegree F)))).comp
          (abelianizedTransfer HW (hHG.preimage f.continuous)) := rfl
    _ = ((abelianizationMap (eG : HG →ₜ* L.field.fixingSubgroup)).comp
        (abelianizationMap (TransferNaturality.subgroupPreimageMap f HG))).comp
          (abelianizedTransfer HW (hHG.preimage f.continuous)) := by
      exact congrArg (fun q => q.comp (abelianizedTransfer HW (hHG.preimage f.continuous))) heq
    _ = _ := by
      exact congrArg (fun q => (abelianizationMap (eG : HG →ₜ* L.field.fixingSubgroup)).comp q)
        ht.symm

/-- The actual subgroup projection is injective on the closed-commutator quotients. -/
theorem fixingWeilAbelianProjection_injective (E : FiniteIntermediateExtension F.Carrier) :
    Function.Injective (E.weilGaloisAbelianProjection (localResidueDegree F)) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (intermediateWeilAbelianEquiv F E).surjective x
  obtain ⟨b, rfl⟩ := (intermediateWeilAbelianEquiv F E).surjective y
  apply congrArg (intermediateWeilAbelianEquiv F E)
  apply WeilReciprocityUniqueness.toGroupAbelianization_injective (E.asPadicField (p := p))
  apply (intermediateGaloisAbelianEquiv F E).injective
  rw [intermediateAbelianEquiv_projection, intermediateAbelianEquiv_projection]
  exact h

/-- A candidate's induced Galois map cancels the candidate on its image. -/
theorem galoisHom_apply_candidate
    (e : CandidateFamily F (canonicalData F) (localResidueDegree F))
    (E : FiniteIntermediateExtension F.Carrier)
    (w : TopologicalAbelianization
      (pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F))) :
    letI := (canonicalData F E).topology
    galoisHom F (canonicalData F) (localResidueDegree F) e E (e E w) =
      E.weilGaloisAbelianProjection (localResidueDegree F) w := by
  let := (canonicalData F E).topology
  change E.weilGaloisAbelianProjection (localResidueDegree F) ((e E).symm (e E w)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]

/-- The actual Galois transfer of a common-closure candidate's unit map. -/
def galoisTransferHom
    (e : CandidateFamily F (canonicalData F) (localResidueDegree F))
    (E L : FiniteIntermediateExtension F.Carrier) (h : E.field ≤ L.field) :
    letI := (canonicalData F E).topology
    E.fieldˣ →ₜ* TopologicalAbelianization L.field.fixingSubgroup := by
  letI := (canonicalData F E).topology
  exact (E.galoisAbelianTransfer L h).comp
    (galoisHom F (canonicalData F) (localResidueDegree F) e E)

/-- The arithmetic transfer square in the actual fixing-subgroup Galois abelianizations. -/
def GaloisTransferRelation
    (e : CandidateFamily F (canonicalData F) (localResidueDegree F)) : Prop :=
  ∀ (E L : FiniteIntermediateExtension F.Carrier) (h : E.field ≤ L.field),
    letI := (canonicalData F E).topology
    letI := (canonicalData F L).topology
    ∀ a : E.fieldˣ, galoisTransferHom F e E L h a =
      galoisHom F (canonicalData F) (localResidueDegree F) e L (E.unitsInclusion L h a)

/-- The actual Weil transfer law is equivalent to the arithmetic Galois transfer square. -/
theorem transferRelation_iff_galoisTransferRelation
    (e : CandidateFamily F (canonicalData F) (localResidueDegree F)) :
    TransferRelation F (canonicalData F) (localResidueDegree F) e ↔
      GaloisTransferRelation F e := by
  constructor
  · intro hW E L h a
    let := (canonicalData F E).topology
    let := (canonicalData F L).topology
    let w := (e E).symm a
    have hw := DFunLike.congr_fun (hW E L h) w
    change e L (E.weilAbelianTransfer L h (localResidueDegree F) w) =
      E.unitsInclusion L h (e E w) at hw
    have hg := congrArg (galoisHom F (canonicalData F) (localResidueDegree F) e L) hw
    rw [galoisHom_apply_candidate] at hg
    change L.weilGaloisAbelianProjection (localResidueDegree F)
      (E.weilAbelianTransfer L h (localResidueDegree F) w) =
      galoisHom F (canonicalData F) (localResidueDegree F) e L
        (E.unitsInclusion L h (e E ((e E).symm a))) at hg
    rw [ContinuousMulEquiv.apply_symm_apply] at hg
    have hs := DFunLike.congr_fun (weilGaloisAbelianProjection_transfer F E L h) w
    change L.weilGaloisAbelianProjection (localResidueDegree F)
      (E.weilAbelianTransfer L h (localResidueDegree F) w) =
        E.galoisAbelianTransfer L h (E.weilGaloisAbelianProjection (localResidueDegree F) w) at hs
    rw [hs] at hg
    exact hg
  · intro hG E L h
    let := (canonicalData F E).topology
    let := (canonicalData F L).topology
    apply MonoidHom.ext
    intro w
    change e L (E.weilAbelianTransfer L h (localResidueDegree F) w) =
      E.unitsInclusion L h (e E w)
    apply (e L).symm.injective
    rw [ContinuousMulEquiv.symm_apply_apply]
    apply fixingWeilAbelianProjection_injective F L
    change L.weilGaloisAbelianProjection (localResidueDegree F)
      (E.weilAbelianTransfer L h (localResidueDegree F) w) =
      galoisHom F (canonicalData F) (localResidueDegree F) e L
        (E.unitsInclusion L h (e E w))
    have hs := DFunLike.congr_fun (weilGaloisAbelianProjection_transfer F E L h) w
    change L.weilGaloisAbelianProjection (localResidueDegree F)
      (E.weilAbelianTransfer L h (localResidueDegree F) w) =
        E.galoisAbelianTransfer L h (E.weilGaloisAbelianProjection (localResidueDegree F) w) at hs
    rw [hs]
    have hg := hG E L h (e E w)
    change E.galoisAbelianTransfer L h
      (galoisHom F (canonicalData F) (localResidueDegree F) e E (e E w)) = _ at hg
    rw [galoisHom_apply_candidate] at hg
    exact hg

end CommonClosure
end Langlands.LocalClassField
