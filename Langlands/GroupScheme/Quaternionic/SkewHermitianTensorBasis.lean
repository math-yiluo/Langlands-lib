import Langlands.GroupScheme.Quaternionic.AntihermitianForm
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Tensor coordinates in an arbitrary quaternionic basis -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.AntihermitianForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V]
  [Module D V] [Module F V] [IsScalarTower F D V] {I : Type w} [Fintype I]
  (B : AntihermitianForm τ V) (b : Module.Basis I D V)
  (R : Type u) [Field R] [Algebra F R]

/-- Coordinates of a base-changed vector in the given division-algebra basis. -/
def tensorBasisCoordinates [DecidableEq I] : R ⊗[F] V ≃ₗ[R] (I → R ⊗[F] D) :=
  ((b.equivFun.restrictScalars F).baseChange F R V (I → D)).trans
    (TensorProduct.piRight F R R (fun _ : I => D))

@[simp]
theorem tensorBasisCoordinates_tmul [DecidableEq I] (r : R) (x : V) (i : I) :
    tensorBasisCoordinates b R (r ⊗ₜ[F] x) i = r ⊗ₜ[F] b.repr x i := by
  simp only [tensorBasisCoordinates, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.restrictScalars_apply, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    Module.Basis.equivFun_apply]

private theorem apply_eq_sum_basis (x y : V) :
    B x y = ∑ i, ∑ j, b.repr x i * B (b i) (b j) * τ (b.repr y j) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  change B.toBilin (∑ i, b.repr x i • b i) (∑ j, b.repr y j • b j) = _
  rw [map_sum B.toBilin, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change B (b.repr x i • b i) (b.repr y j • b j) = _
  rw [B.smul_right, B.smul_left]

variable [DecidableEq I]

/-- The scalar extension of the skew pairing has the usual row expression in
  the scalar-extended basis. -/
theorem tensor_pairing_in_basis (x y : R ⊗[F] V) :
    LinearMap.BilinMap.baseChange R B.toBilin x y =
      ∑ i, ∑ j, tensorBasisCoordinates b R x i * ((1 : R) ⊗ₜ[F] B (b i) (b j)) *
        τ.baseChange R (tensorBasisCoordinates b R y j) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, hx, hx']
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, hy, hy']
    | tmul s y =>
      simp only [LinearMap.BilinMap.baseChange_tmul, tensorBasisCoordinates_tmul,
        FirstKindInvolution.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      have he : B.toBilin x y = B x y := rfl
      rw [he, B.apply_eq_sum_basis b x y]
      simp only [TensorProduct.tmul_sum]

/-- Scaling the pairing by a ground-field scalar scales all Gram coefficients. -/
theorem tensor_pairing_in_basis_scaled (a : F) (x y : R ⊗[F] V) :
    (algebraMap F R a) • LinearMap.BilinMap.baseChange R B.toBilin x y =
      ∑ i, ∑ j, tensorBasisCoordinates b R x i * ((1 : R) ⊗ₜ[F] (a • B (b i) (b j))) *
        τ.baseChange R (tensorBasisCoordinates b R y j) := by
  rw [B.tensor_pairing_in_basis b R]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he (z : D) : (algebraMap F R a) • ((1 : R) ⊗ₜ[F] z) = (1 : R) ⊗ₜ[F] (a • z) := by
    change ((algebraMap F R a) * (1 : R)) ⊗ₜ[F] z = _
    rw [← Algebra.smul_def, TensorProduct.smul_tmul]
  rw [← smul_mul_assoc, ← mul_smul_comm, he]

end Langlands.GroupScheme.Quaternionic.AntihermitianForm
