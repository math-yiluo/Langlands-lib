module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Ideal.Operations

/-! # Comultiplication as a convolution product, and exterior products of linear maps

For a commutative bialgebra `H`, the comultiplication, seen as a point of `H` with values in
`H ⊗[R] H`, is the convolution product of the two tensor inclusions
(`Langlands.Bialgebra.comulPoint_eq_include_mul`).

For linear maps `s : M →ₗ[R] S` and `t : N →ₗ[R] S` into an `R`-algebra, `WithConv.mulTensor s t`
is the map `x ⊗ y ↦ s x * t y` on `M ⊗[R] N`. It is bilinear in `(s, t)` and multiplicative for
the convolution products when `M` and `N` carry comultiplications.
-/

@[expose] public section

open TensorProduct WithConv

namespace Langlands.Bialgebra

variable {R : Type*} [CommSemiring R] {H : Type*} [CommSemiring H] [_root_.Bialgebra R H]

/-- The comultiplication point is the product of the two tensor-factor points. -/
theorem comulPoint_eq_include_mul :
    toConv (Bialgebra.comulAlgHom R H) =
      toConv (Algebra.TensorProduct.includeLeft (R := R) (A := H) (B := H)) *
      toConv (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)) := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  change _ = (_ * _ : WithConv (H →ₐ[R] H ⊗[R] H)) x
  rw [AlgHom.convMul_apply]
  have hid : Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
      Algebra.TensorProduct.includeRight (fun _ _ => .all ..) = AlgHom.id R _ := by
    ext <;> simp
  exact congrArg (fun f : H ⊗[R] H →ₐ[R] H ⊗[R] H => f (Coalgebra.comul x)) hid.symm

end Langlands.Bialgebra

section ExteriorProduct

variable {R M N S : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Semiring S] [Algebra R S]

namespace WithConv

/-- The exterior product of two linear maps into an algebra: apply one map on each tensor factor
and multiply the values. -/
def mulTensor (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    WithConv (M ⊗[R] N →ₗ[R] S) :=
  toConv (LinearMap.mul' R S ∘ₗ TensorProduct.map s.ofConv t.ofConv)

@[simp]
lemma mulTensor_apply_tmul (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S))
    (x : M) (y : N) : (mulTensor s t).ofConv (x ⊗ₜ[R] y) = s.ofConv x * t.ofConv y :=
  rfl

@[simp]
lemma mulTensor_zero_left (t : WithConv (N →ₗ[R] S)) :
    mulTensor (0 : WithConv (M →ₗ[R] S)) t = 0 := by
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [mulTensor_apply_tmul]
  simp

@[simp]
lemma mulTensor_zero_right (s : WithConv (M →ₗ[R] S)) :
    mulTensor s (0 : WithConv (N →ₗ[R] S)) = 0 := by
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [mulTensor_apply_tmul]
  simp

@[simp]
lemma mulTensor_add_left (s₁ s₂ : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor (s₁ + s₂) t = mulTensor s₁ t + mulTensor s₂ t := by
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [mulTensor_apply_tmul]
  simp [add_mul]

@[simp]
lemma mulTensor_add_right (s : WithConv (M →ₗ[R] S)) (t₁ t₂ : WithConv (N →ₗ[R] S)) :
    mulTensor s (t₁ + t₂) = mulTensor s t₁ + mulTensor s t₂ := by
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [mulTensor_apply_tmul]
  simp [mul_add]

@[simp]
lemma mulTensor_smul_left (r : R) (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor (r • s) t = r • mulTensor s t := by
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [mulTensor_apply_tmul]
  simp

@[simp]
lemma mulTensor_smul_right (r : R) (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor s (r • t) = r • mulTensor s t := by
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [mulTensor_apply_tmul]
  simp

end WithConv

namespace AlgHom

variable {A : Type*} [Semiring A] [Algebra R A]

/-- An algebra map composed with multiplication is its own exterior square. -/
@[simp]
lemma toConv_toLinearMap_comp_mul' (g : A →ₐ[R] S) :
    toConv (g.toLinearMap ∘ₗ LinearMap.mul' R A) =
      mulTensor (toConv g.toLinearMap) (toConv g.toLinearMap) := by
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [mulTensor_apply_tmul]
  simp

end AlgHom

end ExteriorProduct

section ExteriorConvolution

variable {R C D S : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
  [AddCommMonoid D] [Module R D] [CoalgebraStruct R D]
  [CommSemiring S] [Algebra R S]

namespace WithConv

/-- The exterior product is multiplicative for the convolution products. -/
@[simp]
lemma mulTensor_convMul (s u : WithConv (C →ₗ[R] S)) (t v : WithConv (D →ₗ[R] S)) :
    mulTensor s t * mulTensor u v = mulTensor (s * u) (t * v) := by
  apply WithConv.ofConv_injective
  unfold mulTensor
  have h := LinearMap.algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' R (S := S))
    (toConv (TensorProduct.map s.ofConv t.ofConv)) (toConv (TensorProduct.map u.ofConv v.ofConv))
  simpa only [map_convMul_map, Algebra.TensorProduct.lmul'_toLinearMap, ofConv_toConv] using h.symm

end WithConv

end ExteriorConvolution
