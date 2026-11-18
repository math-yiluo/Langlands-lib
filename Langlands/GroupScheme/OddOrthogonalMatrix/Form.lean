import Langlands.GroupScheme.OrthogonalMatrix.Basic
import Langlands.GroupScheme.Quaternionic.RadicalFreeQuadratic

/-! # The split odd-dimensional scalar quadratic form -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution

variable (l : Type) [Fintype l] [DecidableEq l]

/-- The odd-dimensional vector coordinates: one anisotropic coordinate followed
by the two halves of a hyperbolic space. -/
abbrev Index := Unit ⊕ (l ⊕ l)

variable (K : Type u) [Field K]

/-- The representative of `z² + ∑ᵢ xᵢyᵢ` on the odd-dimensional split space. -/
def formMatrix : Matrix (Index l) (Index l) K :=
  Matrix.fromBlocks 1 0 0 (OrthogonalMatrix.formMatrix l K)

/-- The scalar quadratic form of `z² + ∑ᵢ xᵢyᵢ`. -/
def form : (scalar K).QuadraticForms (Index l) :=
  Submodule.Quotient.mk (formMatrix l K)

/-- The polar Gram matrix is `diag(2,J)` with `J` the even hyperbolic matrix. -/
def polarMatrix : Matrix (Index l) (Index l) K :=
  Matrix.fromBlocks (2 : Matrix Unit Unit K) 0 0 (OrthogonalMatrix.polarMatrix l K)

@[simp] theorem polar_form : (scalar K).polar (form l K) = polarMatrix l K := by
  rw [form, scalar_polar_mk]
  simp [formMatrix, polarMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_add,
    OrthogonalMatrix.formMatrix_add_transpose, one_add_one_eq_two]

variable {l K}

/-- Multiplication by the polar matrix in odd split coordinates. -/
theorem vecMul_polarMatrix (x : Index l → K) :
    x ᵥ* polarMatrix l K = Sum.elim (fun _ => 2 * x (Sum.inl ()))
      (Sum.elim (fun i => x (Sum.inr (Sum.inr i)))
        (fun i => x (Sum.inr (Sum.inl i)))) := by
  ext i
  rcases i with i | i
  · cases i
    simp [polarMatrix, Matrix.vecMul, dotProduct, Matrix.ofNat_apply]
    ring
  · rcases i with i | i <;>
      simp [polarMatrix, OrthogonalMatrix.polarMatrix, Matrix.vecMul_fromBlocks]

/-- The ordinary value of the split odd quadratic form. -/
theorem quadraticValue_form_eq_zero_iff (x : Index l → K) :
    (scalar K).quadraticValue x (form l K) = 0 ↔
      x (Sum.inl ()) * x (Sum.inl ()) +
        ∑ i, x (Sum.inr (Sum.inl i)) * x (Sum.inr (Sum.inr i)) = 0 := by
  rw [form, scalar_quadraticValue_mk_eq_zero_iff]
  simp [formMatrix, OrthogonalMatrix.formMatrix, Fintype.sum_sum_type, Matrix.one_apply]

/-- A vector in the polar kernel has vanishing hyperbolic coordinates. -/
theorem mem_polarKernel_iff (x : Index l → K) :
    x ∈ LinearMap.ker ((scalar K).polar (form l K)).vecMulLinear ↔
      2 * x (Sum.inl ()) = 0 ∧
      (∀ i, x (Sum.inr (Sum.inl i)) = 0) ∧
      (∀ i, x (Sum.inr (Sum.inr i)) = 0) := by
  rw [LinearMap.mem_ker, polar_form]
  change x ᵥ* polarMatrix l K = 0 ↔ _
  rw [vecMul_polarMatrix]
  constructor
  · intro h
    exact ⟨congrFun h (Sum.inl ()), fun i => congrFun h (Sum.inr (Sum.inr i)),
      fun i => congrFun h (Sum.inr (Sum.inl i))⟩
  · rintro ⟨hz, hx, hy⟩
    funext i
    rcases i with i | i
    · cases i; exact hz
    · rcases i with i | i
      · exact hy i
      · exact hx i

/-- The split odd quadratic form has zero quadratic radical in every
characteristic, including characteristic two. -/
theorem radicalFree_form : (scalar K).IsRadicalFreeQuadratic (form l K) := by
  intro x hq hx
  have hp : x ∈ LinearMap.ker ((scalar K).polar (form l K)).vecMulLinear := by
    rw [LinearMap.mem_ker]
    funext j
    have h := hx (Pi.single j 1)
    rw [sesqForm_single_right, scalar_apply, mul_one] at h
    exact h
  obtain ⟨_, hx0, hy0⟩ := (mem_polarKernel_iff x).1 hp
  rw [quadraticValue_form_eq_zero_iff] at hq
  simp only [hx0, zero_mul, Finset.sum_const_zero, add_zero] at hq
  have hz : x (Sum.inl ()) = 0 := (mul_self_eq_zero.mp hq)
  funext i
  rcases i with i | i
  · cases i; exact hz
  · rcases i with i | i
    · exact hx0 i
    · exact hy0 i

/-- The distinguished axis vector of the odd split space. -/
def axis : Index l → K := Pi.single (Sum.inl ()) 1

omit [Fintype l] in
@[simp] theorem axis_apply_left : axis (l := l) (K := K) (Sum.inl ()) = 1 := by
  simp [axis]

omit [Fintype l] in
@[simp] theorem axis_apply_right (i : l ⊕ l) : axis (l := l) (K := K) (Sum.inr i) = 0 := by
  simp [axis]

omit [Fintype l] in
/-- The distinguished axis vector is nonzero. -/
theorem axis_ne_zero : axis (l := l) (K := K) ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl ())
  simp at this

/-- In characteristic two the polar kernel is exactly the distinguished axis. -/
theorem polarKernel_eq_axis (h2 : (2 : K) = 0) :
    LinearMap.ker ((scalar K).polar (form l K)).vecMulLinear =
      K ∙ axis (l := l) (K := K) := by
  ext x
  rw [mem_polarKernel_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨_, hx, hy⟩
    refine ⟨x (Sum.inl ()), ?_⟩
    funext i
    rcases i with i | i
    · cases i; simp
    · rcases i with i | i <;> simp [hx, hy]
  · rintro ⟨a, rfl⟩
    simp [h2]

/-- Outside characteristic two the polar kernel vanishes. -/
theorem polarKernel_eq_bot (h2 : (2 : K) ≠ 0) :
    LinearMap.ker ((scalar K).polar (form l K)).vecMulLinear = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨hz, hx, hy⟩ := (mem_polarKernel_iff x).1 hx
  have hz0 : x (Sum.inl ()) = 0 := (mul_eq_zero.mp hz).resolve_left h2
  rw [Submodule.mem_bot]
  funext i
  rcases i with i | i
  · cases i; exact hz0
  · rcases i with i | i
    · exact hx i
    · exact hy i

open Classical in
/-- The polar kernel has dimension one in characteristic two and zero otherwise. -/
theorem finrank_polarKernel :
    Module.finrank K (LinearMap.ker ((scalar K).polar (form l K)).vecMulLinear) =
      (if (2 : K) = 0 then 1 else 0) := by
  by_cases h2 : (2 : K) = 0
  · rw [ite_eq_left h2, polarKernel_eq_axis h2, finrank_span_singleton axis_ne_zero]
  · rw [ite_eq_right h2, polarKernel_eq_bot h2, finrank_bot]

end Langlands.GroupScheme.OddOrthogonalMatrix
