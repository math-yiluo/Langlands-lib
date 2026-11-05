import Langlands.GroupScheme.Reductive.CovariantProducts

/-! # Tensors that are covariant in each factor -/

noncomputable section

open TensorProduct Coalgebra

namespace Langlands.GroupScheme.Chevalley

section Kunneth

variable {k M M' N N' : Type*} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup M'] [Module k M'] [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N']

/-- Over a field, a tensor killed by `φ ⊗ id` and by `id ⊗ φ'` lies in the tensor product of
the two kernels. -/
theorem mem_range_map_ker_subtype (φ : M →ₗ[k] N) (φ' : M' →ₗ[k] N') {F : M ⊗[k] M'}
    (h : φ.rTensor M' F = 0) (h' : φ'.lTensor M F = 0) :
    F ∈ LinearMap.range
      (TensorProduct.map (LinearMap.ker φ).subtype (LinearMap.ker φ').subtype) := by
  obtain ⟨G, rfl⟩ :=
    (Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map φ') F).mp h'
  have hG : φ.rTensor (LinearMap.ker φ') G = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := N) _
      (LinearMap.ker φ').injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]
    exact h
  obtain ⟨G', rfl⟩ :=
    (Module.Flat.rTensor_exact (LinearMap.ker φ') (LinearMap.exact_subtype_ker_map φ) G).mp hG
  exact ⟨G', by rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]⟩

end Kunneth

section Covariant

variable {k A C D : Type*} [Field k] [CommRing A] [Bialgebra k A]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]

/-- The linear map whose kernel is the left covariant subspace. -/
theorem leftCovariantSubspace_eq_ker (r : A →ₗ[k] C) (χ : C) :
    leftCovariantSubspace r χ = LinearMap.ker (r.rTensor A ∘ₗ comul - TensorProduct.mk k C A χ) :=
  rfl

/-- A tensor in `A ⊗ A` which is left `r`-covariant of weight `χ` in its first factor and left
`s`-covariant of weight `ψ` in its second factor multiplies into the product of the two
covariant subspaces. -/
theorem mul'_mem_mul_leftCovariantSubspace (r : A →ₗ[k] C) (s : A →ₗ[k] D) (χ : C) (ψ : D)
    {F : A ⊗[k] A}
    (h : (r.rTensor A ∘ₗ comul).rTensor A F = (TensorProduct.mk k C A χ).rTensor A F)
    (h' : (s.rTensor A ∘ₗ comul).lTensor A F = (TensorProduct.mk k D A ψ).lTensor A F) :
    LinearMap.mul' k A F ∈ leftCovariantSubspace r χ * leftCovariantSubspace s ψ := by
  obtain ⟨G, rfl⟩ := mem_range_map_ker_subtype
    (r.rTensor A ∘ₗ comul - TensorProduct.mk k C A χ)
    (s.rTensor A ∘ₗ comul - TensorProduct.mk k D A ψ)
    (F := F) (by rw [LinearMap.rTensor_sub, LinearMap.sub_apply, h, sub_self])
    (by rw [LinearMap.lTensor_sub, LinearMap.sub_apply, h', sub_self])
  rw [← range_coordinateProduct]
  exact ⟨G, rfl⟩

end Covariant

end Langlands.GroupScheme.Chevalley
