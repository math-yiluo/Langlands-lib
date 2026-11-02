import Langlands.Algebra.SeparableTensor
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Permutation of embeddings and tensor coordinates -/

noncomputable section

universe u v w z

open scoped TensorProduct

namespace Langlands.Algebra.SeparableTensor

variable (k : Type u) (K : Type v) (Ω : Type w)
  [CommSemiring k] [CommSemiring K] [CommSemiring Ω] [Algebra k K] [Algebra k Ω]

/-- A coefficient automorphism acts on embeddings by postcomposition. -/
def embeddingPermutation (σ : Ω ≃ₐ[k] Ω) : Equiv.Perm (K →ₐ[k] Ω) :=
  AlgEquiv.arrowCongr (AlgEquiv.refl (R := k) (A₁ := K)) σ

@[simp] theorem embeddingPermutation_apply (σ : Ω ≃ₐ[k] Ω) (τ : K →ₐ[k] Ω) :
    embeddingPermutation k K Ω σ τ = σ.toAlgHom.comp τ := rfl

@[simp] theorem embeddingPermutation_symm (σ : Ω ≃ₐ[k] Ω) :
    (embeddingPermutation k K Ω σ).symm = embeddingPermutation k K Ω σ.symm := rfl

/-- Postcomposition respects the usual order of multiplication of automorphisms. -/
def embeddingPermutationHom : (Ω ≃ₐ[k] Ω) →* Equiv.Perm (K →ₐ[k] Ω) where
  toFun := embeddingPermutation k K Ω
  map_one' := rfl
  map_mul' σ τ := by ext f x; rfl

@[simp] theorem embeddingPermutation_mul (σ τ : Ω ≃ₐ[k] Ω) :
    embeddingPermutation k K Ω (σ * τ) =
      embeddingPermutation k K Ω σ * embeddingPermutation k K Ω τ :=
  (embeddingPermutationHom k K Ω).map_mul σ τ

/-- The integer permutation representation on functions on the embeddings. -/
def embeddingPermutationRepresentation :
    Representation ℤ (Ω ≃ₐ[k] Ω) ((K →ₐ[k] Ω) → ℤ) where
  toFun σ :=
    { toFun := fun m τ => m ((embeddingPermutation k K Ω σ).symm τ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := rfl
  map_mul' σ τ := by
    ext m f
    change m ((embeddingPermutation k K Ω (σ * τ)).symm f) =
      m ((embeddingPermutation k K Ω τ).symm ((embeddingPermutation k K Ω σ).symm f))
    rw [embeddingPermutation_mul]
    rfl

@[simp] theorem embeddingPermutationRepresentation_apply (σ : Ω ≃ₐ[k] Ω)
    (m : (K →ₐ[k] Ω) → ℤ) (τ : K →ₐ[k] Ω) :
    embeddingPermutationRepresentation k K Ω σ m τ = m (σ.symm.toAlgHom.comp τ) := rfl

/-- Reindexing both vectors by an automorphism preserves their dot product. -/
theorem embeddingPermutationRepresentation_dotProduct [Fintype (K →ₐ[k] Ω)]
    (σ : Ω ≃ₐ[k] Ω) (m n : (K →ₐ[k] Ω) → ℤ) :
    (∑ τ, embeddingPermutationRepresentation k K Ω σ m τ *
      embeddingPermutationRepresentation k K Ω σ n τ) = ∑ τ, m τ * n τ :=
  (embeddingPermutation k K Ω σ).symm.sum_comp (fun τ => m τ * n τ)

/-- The reindexing formula for the monomial of a permuted family of units. -/
theorem embeddingPermutationRepresentation_prod [Fintype (K →ₐ[k] Ω)]
    {M : Type z} [CommGroup M] (σ : Ω ≃ₐ[k] Ω)
    (m : (K →ₐ[k] Ω) → ℤ) (a : (K →ₐ[k] Ω) → M) :
    (∏ τ, a (embeddingPermutation k K Ω σ τ) ^ m τ) =
      ∏ τ, a τ ^ embeddingPermutationRepresentation k K Ω σ m τ := by
  rw [← Equiv.prod_comp (embeddingPermutation k K Ω σ)
    (fun τ => a τ ^ embeddingPermutationRepresentation k K Ω σ m τ)]
  apply Finset.prod_congr rfl
  intro τ _
  change a (embeddingPermutation k K Ω σ τ) ^ m τ =
    a (embeddingPermutation k K Ω σ τ) ^
      m ((embeddingPermutation k K Ω σ).symm (embeddingPermutation k K Ω σ τ))
  rw [Equiv.symm_apply_apply]

/-- Tensor evaluation transforms semilinearly under coefficient automorphisms. -/
theorem embeddingEvaluation_map_left (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] K)
    (τ : K →ₐ[k] Ω) :
    embeddingEvaluation k K Ω
        (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k K) x) τ =
      σ (embeddingEvaluation k K Ω x (embeddingPermutation k K Ω σ.symm τ)) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => simp
  | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

section Coordinates

variable {k K Ω} {R : Type z} [CommSemiring R] [Algebra k R]

/-- Evaluate the first tensor factor at an embedding, using the specified coefficient map. -/
def tensorCoordinate (φ : Ω →ₐ[k] R) (τ : K →ₐ[k] Ω) : K ⊗[k] R →ₐ[k] R :=
  Algebra.TensorProduct.lift (φ.comp τ) (AlgHom.id k R) (fun _ _ => Commute.all _ _)

@[simp] theorem tensorCoordinate_tmul (φ : Ω →ₐ[k] R) (τ : K →ₐ[k] Ω)
    (x : K) (r : R) : tensorCoordinate φ τ (x ⊗ₜ r) = φ (τ x) * r := rfl

/-- Twisting the coefficient map permutes the embedding index. -/
theorem tensorCoordinate_comp (φ : Ω →ₐ[k] R) (σ : Ω ≃ₐ[k] Ω) (τ : K →ₐ[k] Ω) :
    tensorCoordinate (φ.comp σ.toAlgHom) τ =
      tensorCoordinate φ (embeddingPermutation k K Ω σ τ) := rfl

/-- Tensor evaluation commutes with any map of the target algebras. -/
theorem tensorCoordinate_natural {R' : Type*} [CommSemiring R'] [Algebra k R']
    (φ : Ω →ₐ[k] R) (ψ : R →ₐ[k] R') (τ : K →ₐ[k] Ω) (x : K ⊗[k] R) :
    tensorCoordinate (ψ.comp φ) τ (Algebra.TensorProduct.lTensor (S := K) K ψ x) =
      ψ (tensorCoordinate φ τ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x r => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Coordinates

end Langlands.Algebra.SeparableTensor
