import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Finite Galois sets and embeddings of stabilizer fixed fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v

namespace Langlands.Algebra.FiniteGaloisOrbits

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

/-- Restriction of an automorphism to a subgroup's fixed field. -/
def restriction (H : Subgroup (L ≃ₐ[k] L)) (σ : L ≃ₐ[k] L) :
    IntermediateField.fixedField H →ₐ[k] L :=
  σ.toAlgHom.comp (IntermediateField.fixedField H).val

omit [IsGalois k L] in
/-- Two restrictions agree precisely when the automorphisms have the same left coset. -/
theorem restriction_eq_iff (H : Subgroup (L ≃ₐ[k] L)) (σ τ : L ≃ₐ[k] L) :
    restriction k L H σ = restriction k L H τ ↔ σ⁻¹ * τ ∈ H := by
  conv_rhs => rw [← IntermediateField.fixingSubgroup_fixedField H,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    change σ.symm (τ x) = x
    apply σ.injective
    have he := DFunLike.congr_fun h (⟨x, hx⟩ : IntermediateField.fixedField H)
    change σ x = τ x at he
    simpa only [AlgEquiv.apply_symm_apply] using he.symm
  · intro h
    ext x
    change σ (x : L) = τ (x : L)
    have hx := congrArg σ (h x x.property)
    change σ (σ.symm (τ x)) = σ x at hx
    simpa only [AlgEquiv.apply_symm_apply] using hx.symm

omit [FiniteDimensional k L] in
/-- Every embedding of a stabilizer fixed field extends to the given normal extension. -/
theorem restriction_surjective (H : Subgroup (L ≃ₐ[k] L)) :
    Function.Surjective (restriction k L H) := by
  intro τ
  let σ : L ≃ₐ[k] L :=
    AlgEquiv.ofBijective (τ.liftNormal L) (AlgHom.normal_bijective k L L _)
  refine ⟨σ, ?_⟩
  ext x
  exact τ.liftNormal_commutes L x

/-- The left cosets of a subgroup are the embeddings of its fixed field. -/
def quotientEmbeddingEquiv (H : Subgroup (L ≃ₐ[k] L)) :
    ((L ≃ₐ[k] L) ⧸ H) ≃ (IntermediateField.fixedField H →ₐ[k] L) :=
  Equiv.ofBijective
    (Quotient.lift (restriction k L H) (fun σ τ h =>
      (restriction_eq_iff k L H σ τ).mpr ((QuotientGroup.leftRel_apply).mp h)))
    ⟨by
      intro a b
      induction a using Quotient.inductionOn with
      | h σ =>
        induction b using Quotient.inductionOn with
        | h τ =>
          intro h
          exact Quotient.sound ((QuotientGroup.leftRel_apply).mpr
            ((restriction_eq_iff k L H σ τ).mp h)),
      fun τ => by
        obtain ⟨σ, hσ⟩ := restriction_surjective k L H τ
        exact ⟨QuotientGroup.mk σ, hσ⟩⟩

@[simp] theorem quotientEmbeddingEquiv_mk (H : Subgroup (L ≃ₐ[k] L))
    (σ : L ≃ₐ[k] L) :
    quotientEmbeddingEquiv k L H (QuotientGroup.mk σ) = restriction k L H σ := rfl

variable {I : Type v} [MulAction (L ≃ₐ[k] L) I]

/-- The field assigned to a point is the fixed field of its stabilizer. -/
def stabilizerField (i : I) : IntermediateField k L :=
  IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[k] L) i)

/-- An orbit is canonically identified with the embeddings of its stabilizer fixed field. -/
def orbitEmbeddingEquiv (i : I) :
    MulAction.orbit (L ≃ₐ[k] L) i ≃ (stabilizerField k L i →ₐ[k] L) :=
  (MulAction.orbitEquivQuotientStabilizer (L ≃ₐ[k] L) i).trans
    (quotientEmbeddingEquiv k L (MulAction.stabilizer (L ≃ₐ[k] L) i))

@[simp] theorem orbitEmbeddingEquiv_symm_restriction (i : I) (σ : L ≃ₐ[k] L) :
    ((orbitEmbeddingEquiv k L i).symm
      (restriction k L (MulAction.stabilizer (L ≃ₐ[k] L) i) σ) : I) = σ • i := by
  change ((MulAction.orbitEquivQuotientStabilizer (L ≃ₐ[k] L) i).symm
    ((quotientEmbeddingEquiv k L _).symm
      ((quotientEmbeddingEquiv k L _) (QuotientGroup.mk σ))) : I) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Postcomposition of embeddings corresponds to the original action on the orbit. -/
theorem orbitEmbeddingEquiv_symm_comp (i : I) (σ : L ≃ₐ[k] L)
    (τ : stabilizerField k L i →ₐ[k] L) :
    ((orbitEmbeddingEquiv k L i).symm (σ.toAlgHom.comp τ) : I) =
      σ • ((orbitEmbeddingEquiv k L i).symm τ : I) := by
  obtain ⟨a, rfl⟩ := restriction_surjective k L
    (MulAction.stabilizer (L ≃ₐ[k] L) i) τ
  have h : σ.toAlgHom.comp
      (restriction k L (MulAction.stabilizer (L ≃ₐ[k] L) i) a) =
      restriction k L (MulAction.stabilizer (L ≃ₐ[k] L) i) (σ * a) := rfl
  rw [h, orbitEmbeddingEquiv_symm_restriction, orbitEmbeddingEquiv_symm_restriction,
    mul_smul]

/-- One intermediate field for each orbit, using a chosen representative. -/
def orbitField (o : MulAction.orbitRel.Quotient (L ≃ₐ[k] L) I) :
    IntermediateField k L :=
  stabilizerField k L o.out

/-- All points are the dependent union of the embeddings of the orbit fields. -/
def sigmaEmbeddingEquiv :
    (Σ o : MulAction.orbitRel.Quotient (L ≃ₐ[k] L) I, orbitField k L o →ₐ[k] L) ≃ I :=
  (Equiv.sigmaCongrRight (fun o : MulAction.orbitRel.Quotient (L ≃ₐ[k] L) I =>
    (orbitEmbeddingEquiv k L o.out).symm)).trans
    (MulAction.selfEquivSigmaOrbits (L ≃ₐ[k] L) I).symm

/-- The dependent union identification is equivariant for postcomposition on each summand. -/
theorem sigmaEmbeddingEquiv_comp (σ : L ≃ₐ[k] L)
    (o : MulAction.orbitRel.Quotient (L ≃ₐ[k] L) I) (τ : orbitField k L o →ₐ[k] L) :
    sigmaEmbeddingEquiv k L ⟨o, σ.toAlgHom.comp τ⟩ =
      σ • sigmaEmbeddingEquiv k L ⟨o, τ⟩ := by
  exact orbitEmbeddingEquiv_symm_comp k L o.out σ τ

/-- A finite Galois set is equivariantly the embeddings of finitely many intermediate fields. -/
theorem exists_finite_fields {I : Type u} [MulAction (L ≃ₐ[k] L) I] [Finite I] :
    ∃ (n : ℕ) (E : Fin n → IntermediateField k L)
      (e : (Σ i, E i →ₐ[k] L) ≃ I),
      ∀ (σ : L ≃ₐ[k] L) (i : Fin n) (τ : E i →ₐ[k] L),
        e ⟨i, σ.toAlgHom.comp τ⟩ = σ • e ⟨i, τ⟩ := by
  classical
  let O := MulAction.orbitRel.Quotient (L ≃ₐ[k] L) I
  let : Fintype O := Fintype.ofFinite O
  let q : Fin (Fintype.card O) ≃ O := (Fintype.equivFin O).symm
  let E : Fin (Fintype.card O) → IntermediateField k L := fun i => orbitField k L (q i)
  let e : (Σ i, E i →ₐ[k] L) ≃ I :=
    (Equiv.sigmaCongrLeft q).trans (sigmaEmbeddingEquiv k L)
  refine ⟨Fintype.card O, E, e, ?_⟩
  intro σ i τ
  exact sigmaEmbeddingEquiv_comp k L σ (q i) τ

end Langlands.Algebra.FiniteGaloisOrbits
