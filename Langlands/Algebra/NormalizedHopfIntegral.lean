import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # A normalized pair of integrals recovers the antipode -/

noncomputable section

open Coalgebra TensorProduct WithConv

namespace Langlands.NormalizedHopfIntegral

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

/-- Contract the second tensor factor with a linear functional. -/
def contract (ℓ : Module.Dual k H) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ ℓ.lTensor H

@[simp]
theorem contract_tmul (ℓ : Module.Dual k H) (a b : H) :
    contract ℓ (a ⊗ₜ[k] b) = ℓ b • a := by
  simp [contract]

/-- The integral transform associated with a coordinate integral and a dual integral. -/
def transform (t : H) (ℓ : Module.Dual k H) : H →ₗ[k] H where
  toFun a := contract ℓ ((1 ⊗ₜ[k] a) * comul (R := k) t)
  map_add' a b := by simp only [tmul_add, add_mul, map_add]
  map_smul' c a := by simp only [tmul_smul, smul_mul_assoc, map_smul, RingHom.id_apply]

@[simp]
theorem transform_apply (t : H) (ℓ : Module.Dual k H) (a : H) :
    transform t ℓ a = contract ℓ ((1 ⊗ₜ[k] a) * comul (R := k) t) := rfl

theorem contract_left_mul (ℓ : Module.Dual k H) (a : H) (z : H ⊗[k] H) :
    contract ℓ ((a ⊗ₜ[k] (1 : H)) * z) = a * contract ℓ z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

theorem id_conv_transform_apply (t : H) (ℓ : Module.Dual k H) (a : H) :
    (toConv (LinearMap.id : H →ₗ[k] H) * toConv (transform t ℓ)).ofConv a =
      contract ℓ (comul (R := k) (a * t)) := by
  rw [LinearMap.convMul_apply, Bialgebra.comul_mul]
  have h (z : H ⊗[k] H) :
      LinearMap.mul' k H (TensorProduct.map LinearMap.id (transform t ℓ) z) =
        contract ℓ (z * comul (R := k) t) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      change x * contract ℓ ((1 ⊗ₜ[k] y) * comul t) =
        contract ℓ ((x ⊗ₜ[k] y) * comul t)
      rw [← contract_left_mul, ← mul_assoc]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  exact h _

/-- The normalized integral transform is the genuine Hopf antipode. -/
theorem transform_eq_antipode (t : H) (ℓ : Module.Dual k H)
    (ht : ∀ a : H, a * t = counit (R := k) a • t)
    (hℓ : ∀ a : H, contract ℓ (comul (R := k) a) = ℓ a • (1 : H))
    (hn : ℓ t = 1) :
    transform t ℓ = HopfAlgebra.antipode k := by
  apply HopfAlgebra.eq_antipode_of_id_convMul_eq_one
  apply WithConv.ext
  ext a
  rw [id_conv_transform_apply, ht, map_smul, map_smul, hℓ, hn, one_smul]
  simp [LinearMap.convOne_def, Algebra.algebraMap_eq_smul_one]

/-- A left convolution integral gives the tensor contraction identity. -/
theorem contract_comul_of_left_integral (ℓ : Module.Dual k H)
    (hℓ : ∀ f : WithConv (Module.Dual k H), f * toConv ℓ = f.ofConv 1 • toConv ℓ)
    (a : H) : contract ℓ (comul (R := k) a) = ℓ a • (1 : H) := by
  apply Module.eval_apply_injective k
  ext f
  have h (z : H ⊗[k] H) :
      f (contract ℓ z) = LinearMap.mul' k k (TensorProduct.map f ℓ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  change f (contract ℓ (comul a)) = f (ℓ a • (1 : H))
  rw [h]
  change (toConv f * toConv ℓ).ofConv a = _
  rw [hℓ]
  simp [mul_comm]

theorem eval_transform_eq_conv (t : H) (ℓ f : Module.Dual k H) (a : H) :
    f (transform t ℓ a) =
      (toConv f * toConv (ℓ ∘ₗ LinearMap.mul k H a)).ofConv t := by
  rw [transform_apply, LinearMap.convMul_apply]
  have h (z : H ⊗[k] H) :
      f (contract ℓ ((1 ⊗ₜ[k] a) * z)) =
        LinearMap.mul' k k (TensorProduct.map f (ℓ ∘ₗ LinearMap.mul k H a) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  exact h _

/-- For an involutive antipode, convolution evaluation at the coordinate integral
has zero left radical. -/
theorem eq_zero_of_forall_conv_eval_eq_zero (t : H) (ℓ : Module.Dual k H)
    (ht : ∀ a : H, a * t = counit (R := k) a • t)
    (hℓ : ∀ f : WithConv (Module.Dual k H), f * toConv ℓ = f.ofConv 1 • toConv ℓ)
    (hn : ℓ t = 1)
    (hS : Function.Involutive (HopfAlgebra.antipode k (A := H)))
    (f : WithConv (Module.Dual k H))
    (hf : ∀ g : WithConv (Module.Dual k H), (f * g).ofConv t = 0) : f = 0 := by
  have hF := transform_eq_antipode t ℓ ht (contract_comul_of_left_integral ℓ hℓ) hn
  apply WithConv.ext
  ext a
  have h := eval_transform_eq_conv t ℓ f.ofConv (HopfAlgebra.antipode k a)
  rw [hf, hF] at h
  change f.ofConv a = 0
  exact (congrArg f.ofConv (hS a)).symm.trans h

end Langlands.NormalizedHopfIntegral
