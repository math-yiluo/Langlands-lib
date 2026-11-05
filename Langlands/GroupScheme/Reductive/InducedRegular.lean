import Langlands.GroupScheme.Chevalley.RegularSubspace
import Langlands.GroupScheme.Unipotent.ScalarExtension

/-! # Left-covariant coordinate subspaces and finite regular subspaces -/

noncomputable section

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding

variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Module K B]
  [Coalgebra K B] {C : Type*} [AddCommGroup C] [Module K C]

/-- The coordinate equation `f(hg) = χ(h)f(g)`, expressed using a linear restriction map.
No subgroup or character properties are needed for this linear construction. -/
def leftCovariantSubspace (r : B →ₗ[K] C) (χ : C) : Submodule K B :=
  LinearMap.ker (r.rTensor B ∘ₗ comul - TensorProduct.mk K C B χ)

theorem mem_leftCovariantSubspace (r : B →ₗ[K] C) (χ : C) (b : B) :
    b ∈ leftCovariantSubspace r χ ↔ r.rTensor B (comul b) = χ ⊗ₜ[K] b := by
  simp [leftCovariantSubspace, sub_eq_zero]

/-- The coordinate equation is equivalent to all its contractions with linear functionals. -/
theorem mem_leftCovariantSubspace_iff (r : B →ₗ[K] C) (χ : C) (b : B) :
    b ∈ leftCovariantSubspace r χ ↔
      ∀ φ : Module.Dual K C, leftAct (φ ∘ₗ r) b = φ χ • b := by
  rw [mem_leftCovariantSubspace]
  have hcontract (φ : Module.Dual K C) :
      TensorProduct.lid K B (φ.rTensor B (r.rTensor B (comul b))) =
        leftAct (φ ∘ₗ r) b := by
    rw [← LinearMap.rTensor_comp_apply]
    rfl
  constructor
  · intro hb φ
    rw [← hcontract, hb]
    simp
  · intro hb
    apply sub_eq_zero.mp
    apply Unipotent.tensor_ext_left
    intro φ
    rw [map_sub, map_sub, hcontract, hb]
    simp

/-- Left covariance is preserved by every right translation of the coordinate coalgebra. -/
theorem rightAct_mem_leftCovariantSubspace (r : B →ₗ[K] C) (χ : C)
    (ψ : Module.Dual K B) {b : B} (hb : b ∈ leftCovariantSubspace r χ) :
    rightAct ψ b ∈ leftCovariantSubspace r χ := by
  rw [mem_leftCovariantSubspace_iff] at hb ⊢
  intro φ
  rw [← rightAct_leftAct, hb, map_smul]

/-- The finite regular span of covariant coordinates is still covariant. -/
theorem regularSpan_le_leftCovariantSubspace (r : B →ₗ[K] C) (χ : C) (S : Finset B)
    (hS : (S : Set B) ⊆ leftCovariantSubspace r χ) :
    regularSpan (K := K) S ≤ leftCovariantSubspace r χ := by
  rw [regularSpan, Submodule.span_le]
  rintro _ ⟨⟨b, ψ⟩, rfl⟩
  exact rightAct_mem_leftCovariantSubspace r χ ψ (hS b.2)

/-- Every finite set of covariant coordinates lies in a finite-dimensional covariant regular
subspace. This does not assert finite-dimensionality of the whole covariant subspace. -/
theorem exists_finite_leftCovariant_regularSubspace (r : B →ₗ[K] C) (χ : C) (S : Finset B)
    (hS : (S : Set B) ⊆ leftCovariantSubspace r χ) :
    ∃ V : Submodule K B, Module.Finite K V ∧ (S : Set B) ⊆ V ∧
      V ≤ leftCovariantSubspace r χ ∧
      ∀ (ψ : Module.Dual K B) (b : B), b ∈ V → rightAct ψ b ∈ V := by
  exact ⟨regularSpan S, inferInstance, subset_regularSpan S,
    regularSpan_le_leftCovariantSubspace r χ S hS,
    fun ψ _ hb => rightAct_mem_regularSpan S ψ hb⟩

end Langlands.GroupScheme.Chevalley
