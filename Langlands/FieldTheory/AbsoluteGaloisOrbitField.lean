import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-! # Embeddings of the fixed field of an absolute Galois stabilizer -/

noncomputable section

universe u v

namespace Langlands.AbsoluteGalois

variable {k : Type u} [Field k]

local notation "Ω" => SeparableClosure k
local notation "Γ" => Ω ≃ₐ[k] Ω

/-- Restrict an automorphism of the separable closure to an intermediate field. -/
abbrev restrictEmbedding (B : IntermediateField k Ω) (σ : Γ) : B →ₐ[k] Ω :=
  σ.toAlgHom.comp B.val

theorem restrictEmbedding_surjective (B : IntermediateField k Ω) :
    Function.Surjective (restrictEmbedding B) := by
  intro f
  have h := IsSepClosed.surjective_domRestrict_of_isSeparable (K := k) B (M := Ω) (E := Ω)
  obtain ⟨g, hg⟩ := h f
  obtain ⟨σ, rfl⟩ := (Algebra.IsAlgebraic.algEquivEquivAlgHom k Ω).surjective g
  exact ⟨σ, hg⟩

private theorem restrictEmbedding_eq_iff (B : IntermediateField k Ω) (σ τ : Γ) :
    restrictEmbedding B σ = restrictEmbedding B τ ↔ σ⁻¹ * τ ∈ B.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have he : σ x = τ x := DFunLike.congr_fun h (⟨x, hx⟩ : B)
    change σ.symm (τ x) = x
    rw [← he, AlgEquiv.symm_apply_apply]
  · intro h
    apply AlgHom.ext
    intro x
    change σ (x : Ω) = τ (x : Ω)
    have he : σ.symm (τ x) = (x : Ω) := h x x.property
    exact (σ.symm_apply_eq.mp he).symm

/-- Embeddings of an intermediate field are the left cosets of its
pointwise fixing subgroup. -/
def fixingCosetEmbeddingEquiv (B : IntermediateField k Ω) :
    (Γ ⧸ B.fixingSubgroup) ≃ (B →ₐ[k] Ω) := by
  let f : Γ ⧸ B.fixingSubgroup → (B →ₐ[k] Ω) :=
    Quotient.lift (restrictEmbedding B) fun σ τ h =>
      (restrictEmbedding_eq_iff B σ τ).mpr (QuotientGroup.leftRel_apply.mp h)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂' a b fun σ τ h => ?_
    exact QuotientGroup.eq.mpr ((restrictEmbedding_eq_iff B σ τ).mp h)
  · intro x
    obtain ⟨σ, rfl⟩ := restrictEmbedding_surjective B x
    exact ⟨QuotientGroup.mk σ, rfl⟩

@[simp]
theorem fixingCosetEmbeddingEquiv_mk (B : IntermediateField k Ω) (σ : Γ) :
    fixingCosetEmbeddingEquiv B (QuotientGroup.mk σ) = restrictEmbedding B σ := rfl

section Orbit

variable {A : Type v} [MulAction (SeparableClosure k ≃ₐ[k] SeparableClosure k) A]

/-- The intermediate field fixed by the stabilizer of a point. -/
def orbitField (x : A) : IntermediateField k Ω :=
  IntermediateField.fixedField (MulAction.stabilizer Γ x)

theorem orbitField_fixingSubgroup (x : A)
    (hx : IsOpen (MulAction.stabilizer Γ x : Set Γ)) :
    (orbitField (k := k) x).fixingSubgroup = MulAction.stabilizer Γ x :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨MulAction.stabilizer Γ x, Subgroup.isClosed_of_isOpen _ hx⟩

/-- For an open stabilizer, the degree of its fixed field is the
cardinality of the orbit. -/
theorem finrank_orbitField (x : A) (hx : IsOpen (MulAction.stabilizer Γ x : Set Γ)) :
    Module.finrank k (orbitField (k := k) x) = Nat.card (MulAction.orbit Γ x) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, orbitField_fixingSubgroup x hx]
  exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Γ x).symm

/-- Embeddings of the field fixed by an open stabilizer correspond to the
points of the original orbit. -/
def orbitFieldEmbeddingEquiv (x : A) (hx : IsOpen (MulAction.stabilizer Γ x : Set Γ)) :
    (orbitField (k := k) x →ₐ[k] Ω) ≃ MulAction.orbit Γ x :=
  (fixingCosetEmbeddingEquiv (orbitField (k := k) x)).symm.trans
    ((Subgroup.quotientEquivOfEq (orbitField_fixingSubgroup x hx)).trans
      (MulAction.orbitEquivQuotientStabilizer Γ x).symm)

@[simp]
theorem orbitFieldEmbeddingEquiv_restrict (x : A)
    (hx : IsOpen (MulAction.stabilizer Γ x : Set Γ)) (σ : Γ) :
    (orbitFieldEmbeddingEquiv x hx (restrictEmbedding (orbitField (k := k) x) σ)).val = σ • x := by
  rw [← fixingCosetEmbeddingEquiv_mk]
  unfold orbitFieldEmbeddingEquiv
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply Γ x σ

/-- Postcomposition of embeddings corresponds to action on the orbit. -/
theorem orbitFieldEmbeddingEquiv_comp (x : A)
    (hx : IsOpen (MulAction.stabilizer Γ x : Set Γ)) (σ : Γ) (f : orbitField (k := k) x →ₐ[k] Ω) :
    (orbitFieldEmbeddingEquiv x hx (σ.toAlgHom.comp f)).val =
      σ • (orbitFieldEmbeddingEquiv x hx f).val := by
  obtain ⟨τ, rfl⟩ := restrictEmbedding_surjective (orbitField (k := k) x) f
  change (orbitFieldEmbeddingEquiv x hx (restrictEmbedding (orbitField (k := k) x) (σ * τ))).val = _
  rw [orbitFieldEmbeddingEquiv_restrict, orbitFieldEmbeddingEquiv_restrict, mul_smul]

end Orbit

end Langlands.AbsoluteGalois
