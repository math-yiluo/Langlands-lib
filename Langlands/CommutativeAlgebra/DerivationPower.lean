import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.CharP.Lemmas

/-! # Prime-power iterates of derivations -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra.DerivationPower

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- Multiplication intertwines a derivation with its two tensor-factor actions. -/
theorem comp_mul (D : Derivation R A A) :
    D.toLinearMap.comp (LinearMap.mul' R A) =
      (LinearMap.mul' R A).comp
        (D.toLinearMap.lTensor A + D.toLinearMap.rTensor A) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, LinearMap.mul'_apply, LinearMap.add_apply,
    LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, map_add, Derivation.coeFn_coe,
    Derivation.leibniz, smul_eq_mul, mul_comm]

/-- The two tensor-factor actions of an endomorphism commute. -/
theorem tensor_factors_commute (f : Module.End R A) :
    Commute (f.lTensor A) (f.rTensor A) := by
  change (f.lTensor A).comp (f.rTensor A) = (f.rTensor A).comp (f.lTensor A)
  rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

variable (D : Derivation R A A) (p r : ℕ) [Fact p.Prime] [CharP R p]

/-- Every prime-power iterate of a derivation still satisfies Leibniz. -/
theorem primePower_leibniz (a b : A) :
    (D.toLinearMap ^ (p ^ r)) (a * b) =
      a * (D.toLinearMap ^ (p ^ r)) b +
        b * (D.toLinearMap ^ (p ^ r)) a := by
  have hp0 : (p : Module.End R (A ⊗[R] A)) = 0 := by
    rw [← map_natCast (algebraMap R (Module.End R (A ⊗[R] A))) p,
      CharP.cast_eq_zero, map_zero]
  have hpow :
      (D.toLinearMap.lTensor A + D.toLinearMap.rTensor A) ^ (p ^ r) =
        D.toLinearMap.lTensor A ^ (p ^ r) +
          D.toLinearMap.rTensor A ^ (p ^ r) := by
    obtain ⟨z, hz⟩ := (tensor_factors_commute D.toLinearMap).exists_add_pow_prime_pow_eq
      (Fact.out : p.Prime) r
    simpa only [hp0, zero_mul, add_zero] using hz
  have h := Module.End.commute_pow_left_of_commute (comp_mul D) (p ^ r)
  rw [hpow, LinearMap.lTensor_pow, LinearMap.rTensor_pow] at h
  have hab := DFunLike.congr_fun h (a ⊗ₜ[R] b)
  simpa only [LinearMap.comp_apply, LinearMap.mul'_apply, LinearMap.add_apply,
    LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, map_add, mul_comm] using hab

/-- The derivation whose underlying linear map is the `p^r`-fold iterate. -/
def primePower : Derivation R A A :=
  Derivation.mk' (D.toLinearMap ^ (p ^ r)) (by
    intro a b
    simpa only [smul_eq_mul] using primePower_leibniz D p r a b)

@[simp]
theorem primePower_toLinearMap :
    (primePower D p r).toLinearMap = D.toLinearMap ^ (p ^ r) := rfl

@[simp]
theorem primePower_apply (a : A) :
    primePower D p r a = (D.toLinearMap ^ (p ^ r)) a := rfl

@[simp]
theorem primePower_zero : primePower D p 0 = D := by
  ext a
  simp [primePower_apply]

/-- Intertwining derivations also intertwines all of their prime-power iterates. -/
theorem primePower_naturality {B : Type w} [CommRing B] [Algebra R B]
    (E : Derivation R B B) (f : A →ₗ[R] B)
    (h : E.toLinearMap.comp f = f.comp D.toLinearMap) :
    (primePower E p r).toLinearMap.comp f =
      f.comp (primePower D p r).toLinearMap :=
  Module.End.commute_pow_left_of_commute h (p ^ r)

end Langlands.Algebra.DerivationPower
