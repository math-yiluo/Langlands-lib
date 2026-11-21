import Langlands.GroupScheme.Quaternionic.AntihermitianForm
import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Skew-hermitian row pairings in tensor coordinates -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  {I : Type} [Fintype I] [DecidableEq I]
  (τ : FirstKindInvolution F D) {H : Matrix I I D} (hH : τ.IsAntihermitian H)
  (R : Type u) [Field R] [Algebra F R]

local notation "M" => coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
local notation "c" => TensorProduct.piRight F R R (fun _ : I => D)
local notation "B" => LinearMap.BilinMap.baseChange R (AntihermitianForm.toBilin (AntihermitianForm.ofMatrix hH))

private theorem tensorGram_pairing (x y : R ⊗[F] (I → D)) :
    B x y = ∑ i, ∑ j, c x i * M i j * τ.baseChange R (c y j) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [_root_.map_add, LinearMap.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, hx, hx']
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [_root_.map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, hy, hy']
    | tmul s y =>
      simp only [LinearMap.BilinMap.baseChange_tmul, AntihermitianForm.ofMatrix_apply,
        sesqForm, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, coefficientEquiv_tmul,
        FirstKindInvolution.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        TensorProduct.tmul_sum]

private theorem sum_pairing_eq_dotProduct (x y : I → R ⊗[F] D) :
    (∑ i, ∑ j, x i * M i j * τ.baseChange R (y j)) = x ⬝ᵥ (M *ᵥ (τ.baseChange R ∘ y)) := by
  simp only [Matrix.mulVec, dotProduct, Function.comp_apply, Finset.mul_sum, mul_assoc]

/-- A nonsingular isotropic row in the extended matrix has an isotropic tensor
  preimage with a normalized partner for the scalar-extended pairing. -/
theorem tensorGram_exists_isotropic_with_partner (hu : IsUnit H)
    {x : I → R ⊗[F] D} {i : I} (hxi : IsUnit (x i))
    (hx : ∑ j, ∑ k, x j * M j k * τ.baseChange R (x k) = 0) :
    ∃ t s : R ⊗[F] (I → D), B t t = 0 ∧ B t s = (1 : R) ⊗ₜ[F] (1 : D) := by
  let A := R ⊗[F] D
  have hM : IsUnit M := (hu.map (Algebra.TensorProduct.includeRight :
    Matrix I I D →ₐ[F] R ⊗[F] Matrix I I D)).map (coefficientEquiv F D R)
  let z : I → A := (↑(hM.unit⁻¹) : Matrix I I A) *ᵥ Pi.single i (↑(hxi.unit⁻¹) : A)
  let y : I → A := τ.baseChange R ∘ z
  have hz : M *ᵥ z = Pi.single i (↑(hxi.unit⁻¹) : A) := by
    change M *ᵥ ((↑(hM.unit⁻¹) : Matrix I I A) *ᵥ _) = _
    rw [Matrix.mulVec_mulVec, hM.mul_val_inv, Matrix.one_mulVec]
  have hy : τ.baseChange R ∘ y = z := by
    ext j
    exact (τ.baseChange R).apply_apply (z j)
  refine ⟨(c).symm x, (c).symm y, ?_, ?_⟩
  · rw [τ.tensorGram_pairing hH R, LinearEquiv.apply_symm_apply]
    exact hx
  · rw [τ.tensorGram_pairing hH R, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      τ.sum_pairing_eq_dotProduct R, hy, hz, dotProduct_single, hxi.mul_val_inv]
    rfl

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
