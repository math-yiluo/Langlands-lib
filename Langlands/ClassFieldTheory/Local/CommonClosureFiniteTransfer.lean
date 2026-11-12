import Langlands.ClassFieldTheory.Local.CommonClosureFiniteRestrictions
import Langlands.ClassFieldTheory.Local.DenseTransferNaturality
import Langlands.ClassFieldTheory.Local.FiniteCupTransfer

/-! # Finite restriction commutes with actual fixing-subgroup transfer -/

noncomputable section

namespace Langlands.LocalClassField.FiniteQuotientTransport

open ClassFieldTheory.Local

universe u

section RelativeSubgroup

variable (A B C : Type u) [Field A] [Field B] [Field C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- The relative Galois subgroup is precisely the automorphisms fixing
the image of the middle field. -/
theorem mem_relativeGaloisSubgroup_iff (σ : Gal(C/A)) :
    σ ∈ relativeGaloisSubgroup A B C ↔
      ∀ b : B, σ (algebraMap B C b) = algebraMap B C b := by
  constructor
  · rintro ⟨τ, rfl⟩ b
    exact τ.commutes b
  · intro hσ
    exact ⟨AlgEquiv.ofRingEquiv (f := (σ : C ≃+* C)) hσ, rfl⟩

end RelativeSubgroup

variable (K : Type u) [Field K]
  (E L : FiniteIntermediateExtension K) (hEL : E.field ≤ L.field)
  (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
  (hLM : L.field ≤ M.toIntermediateField)

/-- A finite restriction fixes the middle field exactly when the original
common-closure automorphism does. -/
theorem finiteRestriction_mem_relativeGaloisSubgroup (σ : E.field.fixingSubgroup) :
    letI : Algebra E.field L.field := (IntermediateField.inclusion hEL).toAlgebra
    letI := finiteRestrictionAlgebra K E M (hEL.trans hLM)
    letI := finiteRestrictionAlgebra K L M hLM
    letI : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
    finiteRestrictionHom K E M (hEL.trans hLM) σ ∈
        relativeGaloisSubgroup E.field L.field M ↔
      σ ∈ L.field.fixingSubgroup.subgroupOf E.field.fixingSubgroup := by
  let : Algebra E.field L.field := (IntermediateField.inclusion hEL).toAlgebra
  let := finiteRestrictionAlgebra K E M (hEL.trans hLM)
  let := finiteRestrictionAlgebra K L M hLM
  let : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
  rw [mem_relativeGaloisSubgroup_iff]
  change (∀ b : L.field,
    finiteRestrictionHom K E M (hEL.trans hLM) σ
      (IntermediateField.inclusion hLM b) = IntermediateField.inclusion hLM b) ↔
        σ.val ∈ L.field.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have hh := congrArg (fun z : M => (z : AlgebraicClosure K)) (h ⟨x, hx⟩)
    rw [finiteRestrictionHom_apply] at hh
    exact hh
  · intro h b
    apply Subtype.ext
    rw [finiteRestrictionHom_apply]
    exact h b b.property

/-- Finite restriction of an automorphism in the smaller fixing subgroup
is unchanged by restricting scalars to the larger base. -/
theorem finiteRestriction_restrictScalars
    (σ : L.field.fixingSubgroup) :
    letI : Algebra E.field L.field := (IntermediateField.inclusion hEL).toAlgebra
    letI := finiteRestrictionAlgebra K E M (hEL.trans hLM)
    letI := finiteRestrictionAlgebra K L M hLM
    letI : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
    (finiteRestrictionHom K L M hLM σ).restrictScalars E.field =
      finiteRestrictionHom K E M (hEL.trans hLM)
        (subgroupInclusion (IntermediateField.fixingSubgroup_antitone hEL) σ) := by
  let : Algebra E.field L.field := (IntermediateField.inclusion hEL).toAlgebra
  let := finiteRestrictionAlgebra K E M (hEL.trans hLM)
  let := finiteRestrictionAlgebra K L M hLM
  let : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change (finiteRestrictionHom K L M hLM σ x : AlgebraicClosure K) =
    (finiteRestrictionHom K E M (hEL.trans hLM)
      (subgroupInclusion (IntermediateField.fixingSubgroup_antitone hEL) σ) x :
        AlgebraicClosure K)
  rw [finiteRestrictionHom_apply, finiteRestrictionHom_apply]
  rfl

variable [PerfectField K]

/-- The actual common-closure Galois transfer viewed in a finite
relative Galois abelianization. -/
def finiteTransferHom :
    letI := finiteRestrictionAlgebra K L M hLM
    TopologicalAbelianization E.field.fixingSubgroup →* Abelianization Gal(M/L.field) := by
  letI := finiteRestrictionAlgebra K L M hLM
  exact (finiteAbelianRestriction K L M hLM).comp
    (E.galoisAbelianTransfer L hEL).toMonoidHom

/-- Actual finite-coset transfer commutes with restriction to a finite
Galois overfield, with the subgroup identified by restriction of scalars. -/
theorem finiteRestriction_transfer (σ : E.field.fixingSubgroup) :
    letI : Algebra E.field L.field := (IntermediateField.inclusion hEL).toAlgebra
    letI := finiteRestrictionAlgebra K E M (hEL.trans hLM)
    letI := finiteRestrictionAlgebra K L M hLM
    letI : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K L.field M := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional E.field M := FiniteDimensional.right K E.field M
    letI : FiniteDimensional L.field M := FiniteDimensional.right K L.field M
    letI := absoluteFixingFiniteIndex K L.field
    MonoidHom.transfer
        (Abelianization.of.comp
          (relativeGaloisSubgroupEquiv E.field L.field M).symm.toMonoidHom)
        (finiteRestrictionHom K E M (hEL.trans hLM) σ) =
      MonoidHom.transfer
        ((Abelianization.of.comp (finiteRestrictionHom K L M hLM)).comp
          (subgroupOfEquiv (IntermediateField.fixingSubgroup_antitone hEL)).toMulEquiv.toMonoidHom)
        σ := by
  let : Algebra E.field L.field := (IntermediateField.inclusion hEL).toAlgebra
  let := finiteRestrictionAlgebra K E M (hEL.trans hLM)
  let := finiteRestrictionAlgebra K L M hLM
  let : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E.field M := FiniteDimensional.right K E.field M
  let : FiniteDimensional L.field M := FiniteDimensional.right K L.field M
  let := absoluteFixingFiniteIndex K L.field
  let H := relativeGaloisSubgroup E.field L.field M
  let J := L.field.fixingSubgroup.subgroupOf E.field.fixingSubgroup
  let rE := finiteRestrictionHom K E M (hEL.trans hLM)
  let rL := finiteRestrictionHom K L M hLM
  let eG := subgroupOfEquiv (IntermediateField.fixingSubgroup_antitone hEL)
  let eH := relativeGaloisSubgroupEquiv E.field L.field M
  let ϕ : H →* Abelianization Gal(M/L.field) := Abelianization.of.comp eH.symm.toMonoidHom
  let ϕ' : J →* Abelianization Gal(M/L.field) :=
    (Abelianization.of.comp rL).comp eG.toMulEquiv.toMonoidHom
  have hJ : ∀ (_ : Unit) (τ : E.field.fixingSubgroup),
      τ ∈ J ↔ (1 : Gal(M/E.field))⁻¹ * rE τ * 1 ∈ H := by
    intro _ τ
    dsimp only [J, rE, H]
    simpa only [inv_one, one_mul, mul_one] using
      (finiteRestriction_mem_relativeGaloisSubgroup K E L hEL M hLM τ).symm
  change MonoidHom.transfer ϕ (rE σ) = MonoidHom.transfer ϕ' σ
  rw [GroupTheory.Transfer.transfer_comp_eq_prod_of_conj
    (ψ := rE) (t := fun _ : Unit => (1 : Gal(M/E.field)))
    (K := fun _ : Unit => J) (hK := hJ) ϕ (fun _ => ϕ') ?_ ?_ ?_ σ,
    Fintype.prod_unique]
  · intro _ τ
    change Abelianization.of (rL (eG τ)) =
      Abelianization.of (eH.symm ⟨(1 : Gal(M/E.field))⁻¹ * rE τ * 1, _⟩)
    apply congrArg Abelianization.of
    apply eH.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change (rL (eG τ)).restrictScalars E.field = (1 : Gal(M/E.field))⁻¹ * rE τ * 1
    simp only [inv_one, one_mul, mul_one]
    calc
      _ = rE (subgroupInclusion (IntermediateField.fixingSubgroup_antitone hEL) (eG τ)) :=
        finiteRestriction_restrictScalars K E L hEL M hLM (eG τ)
      _ = rE τ := by congr 1
  · intro g
    obtain ⟨τ, hτ⟩ := finiteRestriction_surjective K E M (hEL.trans hLM) g
    change finiteRestrictionHom K E M (hEL.trans hLM) τ = g at hτ
    exact ⟨(), τ, 1, H.one_mem, by simpa only [mul_one] using hτ.symm⟩
  · intro _ _ _ _ _ _
    rfl

/-- Actual finite restrictions carry the topological transfer between
literal fixing subgroups to the actual finite relative Galois transfer. -/
theorem finiteAbelianRestriction_transfer
    (x : TopologicalAbelianization E.field.fixingSubgroup) :
    letI : Algebra E.field L.field := (IntermediateField.inclusion hEL).toAlgebra
    letI := finiteRestrictionAlgebra K E M (hEL.trans hLM)
    letI := finiteRestrictionAlgebra K L M hLM
    letI : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K L.field M := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional E.field M := FiniteDimensional.right K E.field M
    letI : FiniteDimensional L.field M := FiniteDimensional.right K L.field M
    finiteAbelianRestriction K L M hLM (E.galoisAbelianTransfer L hEL x) =
      relativeGaloisAbelianTransfer E.field L.field M
        (finiteAbelianRestriction K E M (hEL.trans hLM) x) := by
  let : Algebra E.field L.field := (IntermediateField.inclusion hEL).toAlgebra
  let := finiteRestrictionAlgebra K E M (hEL.trans hLM)
  let := finiteRestrictionAlgebra K L M hLM
  let : IsScalarTower E.field L.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K E.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E.field M := FiniteDimensional.right K E.field M
  let : FiniteDimensional L.field M := FiniteDimensional.right K L.field M
  let := absoluteFixingFiniteIndex K L.field
  let J := L.field.fixingSubgroup.subgroupOf E.field.fixingSubgroup
  let eG := subgroupOfEquiv (IntermediateField.fixingSubgroup_antitone hEL)
  let eH := relativeGaloisSubgroupEquiv E.field L.field M
  let q : TopologicalAbelianization J →* Abelianization Gal(M/L.field) :=
    (finiteAbelianRestriction K L M hLM).comp
      (abelianizationMap (eG : J →ₜ* L.field.fixingSubgroup)).toMonoidHom
  have hq : q.comp (abelianizationProjection J).toMonoidHom =
      ((Abelianization.of.comp (finiteRestrictionHom K L M hLM)).comp
        eG.toMulEquiv.toMonoidHom) := by
    apply MonoidHom.ext
    intro τ
    change finiteAbelianRestriction K L M hLM
      (abelianizationProjection _ (eG τ)) = Abelianization.of
        (finiteRestrictionHom K L M hLM (eG τ))
    exact finiteAbelianRestriction_projection K L M hLM (eG τ)
  induction x using QuotientGroup.induction_on with
  | H σ =>
    change q (MonoidHom.transfer (abelianizationProjection J).toMonoidHom σ) =
      relativeGaloisAbelianTransfer E.field L.field M
        (finiteAbelianRestriction K E M (hEL.trans hLM) (abelianizationProjection _ σ))
    rw [finiteAbelianRestriction_projection,
      ← GroupTheory.Transfer.transfer_comp, hq]
    change MonoidHom.transfer
        ((Abelianization.of.comp (finiteRestrictionHom K L M hLM)).comp
          eG.toMulEquiv.toMonoidHom) σ =
      (Abelianization.map eH.symm.toMonoidHom)
        (MonoidHom.transfer Abelianization.of
          (finiteRestrictionHom K E M (hEL.trans hLM) σ))
    rw [← GroupTheory.Transfer.transfer_comp]
    exact (finiteRestriction_transfer K E L hEL M hLM σ).symm

end Langlands.LocalClassField.FiniteQuotientTransport
