import Langlands.Algebra.EmbeddingPermutation
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.MulAction

/-! # Continuous permutation of embeddings -/

noncomputable section

universe u v w

namespace Langlands.Algebra.SeparableTensor

variable (k : Type u) (K : Type v) (Ω : Type w)
  [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]

/-- Postcomposition, as a group action on the algebra embeddings. -/
@[instance_reducible]
def embeddingMulAction : MulAction (Ω ≃ₐ[k] Ω) (K →ₐ[k] Ω) :=
  MulAction.compHom _ (embeddingPermutationHom k K Ω)

attribute [local instance] embeddingMulAction

/-- An embedding is fixed exactly when every element of its image field is fixed. -/
theorem embedding_stabilizer_eq (τ : K →ₐ[k] Ω) :
    MulAction.stabilizer (Ω ≃ₐ[k] Ω) τ = τ.fieldRange.fixingSubgroup := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, IntermediateField.mem_fixingSubgroup_iff]
  change σ.toAlgHom.comp τ = τ ↔ ∀ x ∈ τ.fieldRange, σ x = x
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact DFunLike.congr_fun h y
  · intro h
    ext y
    exact h (τ y) (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)

variable [finiteK : FiniteDimensional k K]

/-- The stabilizer is open for the Krull topology on the coefficient automorphisms. -/
theorem embedding_stabilizer_isOpen (τ : K →ₐ[k] Ω) :
    IsOpen (MulAction.stabilizer (Ω ≃ₐ[k] Ω) τ : Set (Ω ≃ₐ[k] Ω)) := by
  rw [embedding_stabilizer_eq]
  let : FiniteDimensional k τ.fieldRange := τ.equivFieldRange.toLinearEquiv.finiteDimensional
  exact τ.fieldRange.fixingSubgroup_isOpen

section Embeddings

variable [TopologicalSpace (K →ₐ[k] Ω)] [DiscreteTopology (K →ₐ[k] Ω)]

/-- The action on discrete embeddings is continuous for the Krull topology. -/
theorem embedding_continuousSMul : ContinuousSMul (Ω ≃ₐ[k] Ω) (K →ₐ[k] Ω) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (embedding_stabilizer_isOpen k K Ω)

/-- Continuous postcomposition on the discrete embedding set. -/
def embeddingContinuousPermutation :
    C((Ω ≃ₐ[k] Ω) × (K →ₐ[k] Ω), (K →ₐ[k] Ω)) where
  toFun p := embeddingPermutation k K Ω p.1 p.2
  continuous_toFun := by
    let := embedding_continuousSMul k K Ω
    exact continuous_smul

@[simp] theorem embeddingContinuousPermutation_apply (σ : Ω ≃ₐ[k] Ω) (τ : K →ₐ[k] Ω) :
    embeddingContinuousPermutation k K Ω (σ, τ) = σ.toAlgHom.comp τ := rfl

end Embeddings

variable [Finite (K →ₐ[k] Ω)]

/-- The continuous inverse-pullback action on integer functions on the finite embedding set. -/
def embeddingContinuousRepresentation :
    C((Ω ≃ₐ[k] Ω) × ((K →ₐ[k] Ω) → ℤ), ((K →ₐ[k] Ω) → ℤ)) where
  toFun p := embeddingPermutationRepresentation k K Ω p.1 p.2
  continuous_toFun := by
    let : TopologicalSpace (K →ₐ[k] Ω) := ⊥
    let : DiscreteTopology (K →ₐ[k] Ω) := ⟨rfl⟩
    rw [continuous_prod_of_discrete_right]
    intro m
    apply continuous_pi
    intro τ
    exact (continuous_of_discreteTopology (f := m)).comp
      ((embeddingContinuousPermutation k K Ω).continuous.comp
        (continuous_inv.prodMk continuous_const))

include finiteK in
@[simp] theorem embeddingContinuousRepresentation_apply (σ : Ω ≃ₐ[k] Ω)
    (m : (K →ₐ[k] Ω) → ℤ) (τ : K →ₐ[k] Ω) :
    embeddingContinuousRepresentation k K Ω (σ, m) τ = m (σ.symm.toAlgHom.comp τ) := rfl

end Langlands.Algebra.SeparableTensor
