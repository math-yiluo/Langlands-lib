import Langlands.Representation.TensorProduct.ProductFunctionEvaluation

/-! Linear lifting into tensors of functions. -/

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

namespace Langlands

variable {R ι : Type*} [Field R] [Fintype ι]
  {X V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  {W : Type*} [AddCommGroup W] [Module R W]
  (e : ∀ i, V i →ₗ[R] (X i → R)) (he : ∀ i, Function.Injective (e i))
  (f : W →ₗ[R] ((∀ i, X i) → R))

/-- If every value of a linear map is a tensor of functions, its unique
coefficient tensors form a linear map. -/
def functionTensorLinearLift (hf : ∀ w, f w ∈ LinearMap.range (functionTensorEvaluation e)) :
    W →ₗ[R] (⨂[R] i, V i) :=
  (LinearEquiv.ofInjective (functionTensorEvaluation e)
    (functionTensorEvaluation_injective e he)).symm.toLinearMap ∘ₗ
      f.codRestrict _ hf

@[simp]
theorem functionTensorLinearLift_evaluate
    (hf : ∀ w, f w ∈ LinearMap.range (functionTensorEvaluation e)) (w : W) :
    functionTensorEvaluation e (functionTensorLinearLift e he f hf w) = f w := by
  exact LinearEquiv.ofInjective_symm_apply (functionTensorEvaluation e)
    (h := functionTensorEvaluation_injective e he)
    ⟨f w, hf w⟩

include he in
/-- A linear family with finite-dimensional coordinate slices has a linear
tensor lift. The finite-dimensional subspaces may depend on the input. -/
theorem exists_linearTensor_of_finiteDimensional_slices [DecidableEq ι]
    (h : ∀ w, ∃ P : ∀ i, Submodule R (V i), (∀ i, FiniteDimensional R (P i)) ∧
      ∀ i x, ∃ v : P i, e i v.val = fun y => f w (Function.update x i y)) :
    ∃ g : W →ₗ[R] (⨂[R] i, V i), ∀ w, functionTensorEvaluation e (g w) = f w := by
  have hf (w : W) : f w ∈ LinearMap.range (functionTensorEvaluation e) := by
    obtain ⟨P, hP, hs⟩ := h w
    obtain ⟨t, ht⟩ := exists_tensor_of_finiteDimensional_slices e he P (f w) hs
    exact ⟨PiTensorProduct.mapIncl P t, ht⟩
  exact ⟨functionTensorLinearLift e he f hf, functionTensorLinearLift_evaluate e he f hf⟩

end Langlands
