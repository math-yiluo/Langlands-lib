import Langlands.Representation.TensorProduct.ProductFunctionEvaluation

/-! One-coordinate slices of a tensor of functions and factor operators. -/

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

namespace Langlands

variable {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι]
  {X V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  (e : ∀ i, V i →ₗ[R] (X i → R))

private def sliceEvaluation (i : ι) (x : ∀ j, X j) :
    (⨂[R] j, V j) →ₗ[R] (X i → R) where
  toFun t y := functionTensorEvaluation e t (Function.update x i y)
  map_add' t u := funext fun y =>
    congrFun ((functionTensorEvaluation e).map_add t u) (Function.update x i y)
  map_smul' a t := funext fun y =>
    congrFun ((functionTensorEvaluation e).map_smul a t) (Function.update x i y)

private theorem sliceEvaluation_tprod (i : ι) (x : ∀ j, X j) (v : ∀ j, V j) :
    sliceEvaluation e i x (PiTensorProduct.tprod R v) =
      e i ((∏ j ∈ Finset.univ.erase i, e j (v j) (x j)) • v i) := by
  funext y
  change functionTensorEvaluation e (PiTensorProduct.tprod R v) (Function.update x i y) = _
  rw [functionTensorEvaluation_tprod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    Function.update_self, map_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

private theorem sliceEvaluation_mem_range (i : ι) (x : ∀ j, X j) (t : ⨂[R] j, V j) :
    sliceEvaluation e i x t ∈ LinearMap.range (e i) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    rw [map_smul, sliceEvaluation_tprod, ← map_smul]
    exact LinearMap.mem_range_self _ _
  | add t u ht hu =>
    rw [map_add]
    exact (LinearMap.range (e i)).add_mem ht hu

/-- The vector in a distinguished factor obtained by evaluating all the other factors. -/
def functionTensorSlice (i : ι) (he : Function.Injective (e i)) (x : ∀ j, X j) :
    (⨂[R] j, V j) →ₗ[R] V i :=
  (LinearEquiv.ofInjective (e i) he).symm.toLinearMap ∘ₗ
    (sliceEvaluation e i x).codRestrict _ (sliceEvaluation_mem_range e i x)

@[simp]
theorem functionTensorSlice_evaluate (i : ι) (he : Function.Injective (e i)) (x : ∀ j, X j)
    (t : ⨂[R] j, V j) (y : X i) :
    e i (functionTensorSlice e i he x t) y =
      functionTensorEvaluation e t (Function.update x i y) := by
  change e i ((LinearEquiv.ofInjective (e i) he).symm
    ⟨sliceEvaluation e i x t, sliceEvaluation_mem_range e i x t⟩) y = _
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

theorem functionTensorSlice_tprod (i : ι) (he : Function.Injective (e i)) (x : ∀ j, X j)
    (v : ∀ j, V j) :
    functionTensorSlice e i he x (PiTensorProduct.tprod R v) =
      (∏ j ∈ Finset.univ.erase i, e j (v j) (x j)) • v i := by
  apply he
  funext y
  rw [functionTensorSlice_evaluate]
  exact congrFun (sliceEvaluation_tprod e i x v) y

/-! Applying an operator at a single factor. -/

omit [Fintype ι] in
/-- An endomorphism acting on one factor of the tensor product. -/
def tensorCoordinateEnd (i : ι) (a : Module.End R (V i)) : Module.End R (⨂[R] j, V j) :=
  PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i a)

theorem functionTensorSlice_tensorCoordinateEnd (i : ι) (he : Function.Injective (e i))
    (x : ∀ j, X j) (a : Module.End R (V i)) (t : ⨂[R] j, V j) :
    functionTensorSlice e i he x (tensorCoordinateEnd i a t) =
      a (functionTensorSlice e i he x t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, tensorCoordinateEnd, PiTensorProduct.map_tprod, functionTensorSlice_tprod]
    have hprod :
        (∏ j ∈ Finset.univ.erase i,
          e j (Function.update (fun _ => LinearMap.id) i a j (v j)) (x j)) =
          ∏ j ∈ Finset.univ.erase i, e j (v j) (x j) := by
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hj).1, LinearMap.id_apply]
    rw [hprod, Function.update_self]
  | add t u ht hu => simp only [map_add, ht, hu]

omit [Fintype ι] in
theorem tensorCoordinateEnd_intertwines
    {W : ι → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module R (W j)]
    (p : ∀ j, V j →ₗ[R] W j) (i : ι) (a : Module.End R (V i)) (b : Module.End R (W i))
    (h : (p i).comp a = b.comp (p i)) (t : ⨂[R] j, V j) :
    PiTensorProduct.map p (tensorCoordinateEnd i a t) =
      tensorCoordinateEnd i b (PiTensorProduct.map p t) := by
  simp only [tensorCoordinateEnd, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  congr 2
  funext j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using h
  · simp only [Function.update_of_ne hj, LinearMap.comp_id, LinearMap.id_comp]

/-- An identity of all slices in one coordinate determines the identity
of the tensors. In particular, applying an operator in every such slice
is equivalent to applying the operator on the distinguished factor. -/
theorem eq_tensorCoordinateEnd_of_slices (he : ∀ i, Function.Injective (e i))
    (i : ι) (a : Module.End R (V i)) (s t : ⨂[R] j, V j)
    (h : ∀ x, functionTensorSlice e i (he i) x s =
      a (functionTensorSlice e i (he i) x t)) :
    s = tensorCoordinateEnd i a t := by
  apply functionTensorEvaluation_injective e he
  funext x
  rw [← Function.update_eq_self i x,
    ← functionTensorSlice_evaluate e i (he i),
    ← functionTensorSlice_evaluate e i (he i),
    functionTensorSlice_tensorCoordinateEnd, h]

end Langlands
