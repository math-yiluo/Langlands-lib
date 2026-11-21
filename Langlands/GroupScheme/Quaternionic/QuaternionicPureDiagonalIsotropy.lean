import Langlands.GroupScheme.Quaternionic.QuaternionicPureTensorCoefficient
import Mathlib.RingTheory.Flat.Basic

/-! # The scalar condition on zeros of a pure-line diagonal skew form -/

noncomputable section

universe u w

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

/-- A nonzero tuple solving the root-line coefficient equation for quaternion
  coefficients written in two quadratic-field coordinates. -/
def HasNonzeroSkewNormZero {R : Type*} {I : Type*} [CommRing R] [Fintype I]
    (a : I → R) (c d : R) : Prop :=
  ∃ u₀ u₁ v₀ v₁ : I → R,
    (∃ i, u₀ i ≠ 0 ∨ u₁ i ≠ 0 ∨ v₀ i ≠ 0 ∨ v₁ i ≠ 0) ∧
    ∑ i, a i * (u₀ i ^ 2 - c * u₁ i ^ 2 + d * (v₀ i ^ 2 - c * v₁ i ^ 2)) = 0

/-- Injective scalar maps preserve the equation and the nonzero witness. -/
theorem HasNonzeroSkewNormZero.map {R S : Type*} {I : Type*} [CommRing R] [CommRing S]
    [Fintype I] {a : I → R} {c d : R} (h : HasNonzeroSkewNormZero a c d)
    (g : R →+* S) (hg : Function.Injective g) : HasNonzeroSkewNormZero (g ∘ a) (g c) (g d) := by
  obtain ⟨u₀, u₁, v₀, v₁, ⟨i, hi⟩, heq⟩ := h
  refine ⟨g ∘ u₀, g ∘ u₁, g ∘ v₀, g ∘ v₁, ⟨i, ?_⟩, ?_⟩
  · simpa only [Function.comp_apply, map_ne_zero_iff g hg] using hi
  · simpa only [Function.comp_apply, map_sum, map_mul, map_add, map_sub, map_pow, map_zero]
      using congrArg g heq

end Langlands.GroupScheme.Quaternionic

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] (Q : QuatData F D)
  (R : Type u) [Field R] [Algebra F R] {I : Type w} [Fintype I]
  (τ : FirstKindInvolution F D)

local notation "E" => field Q.c
local notation "r" => (root : field Q.c)
local notation "P" => Q.presentation R
local notation "f" => algebraMap F R

/-- A nonzero isotropic row for a pure-line diagonal skew form has nonzero
  scalar coordinates satisfying the root-line coefficient equation. -/
theorem exists_normCoordinates_of_pureDiagonal_isotropic (hbar : ∀ z, τ z = Q.bar z)
    (a : I → R) (z : I → R ⊗[F] D)
    (hz : z ≠ 0) (h : ∑ i, z i * (a i ⊗ₜ[F] Q.x) * τ.baseChange R (z i) = 0) :
    HasNonzeroSkewNormZero a (f Q.c) (f Q.δ) := by
  classical
  choose u₀ u₁ hu using fun i => Q.exists_quadraticTensorCoordinates R ((P).fst (z i))
  choose v₀ v₁ hv using fun i => Q.exists_quadraticTensorCoordinates R ((P).snd (z i))
  have hδ : (P).δ = (1 : E) ⊗ₜ[F] f Q.δ := by
    change algebraMap F (E ⊗[F] R) Q.δ =
      (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R) (f Q.δ)
    exact (Algebra.TensorProduct.includeRight.commutes Q.δ).symm
  have hco (i : I) : Q.fstR R (z i * (a i ⊗ₜ[F] Q.x) * τ.baseChange R (z i)) =
      r ⊗ₜ[F] (a i * (u₀ i ^ 2 - f Q.c * u₁ i ^ 2 + f Q.δ * (v₀ i ^ 2 - f Q.c * v₁ i ^ 2))) := by
    rw [Q.fstR_mul_pure_mul_baseChange R τ hbar, hu i, hv i, Q.presentation_c,
      Q.quadraticTensor_mul_conjugate R, Q.quadraticTensor_mul_conjugate R, hδ,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  refine ⟨u₀, u₁, v₀, v₁, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    apply hz
    funext i
    have h₁ : (P).fst (z i) = 0 := by rw [hu i, (hn i).1, (hn i).2.1]; simp
    have h₂ : (P).snd (z i) = 0 := by rw [hv i, (hn i).2.2.1, (hn i).2.2.2]; simp
    rw [← (P).decompose (z i), h₁, h₂, map_zero, mul_zero, add_zero, Pi.zero_apply]
  · let s := ∑ i, a i * (u₀ i ^ 2 - f Q.c * u₁ i ^ 2 + f Q.δ * (v₀ i ^ 2 - f Q.c * v₁ i ^ 2))
    have hs : r ⊗ₜ[F] s = 0 := by
      have h' := congrArg (Q.fstR R) h
      simpa only [map_sum, hco, ← TensorProduct.tmul_sum, map_zero, s] using h'
    have hr : r ≠ 0 := by
      intro h0
      have hx := Q.basis.ne_zero 1
      rw [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1, ← Q.ι_root, h0, map_zero] at hx
      exact hx rfl
    have hu : IsUnit (r ⊗ₜ[F] (1 : R)) := (isUnit_iff_ne_zero.mpr hr).map (Q.const R)
    have hzero : (1 : E) ⊗ₜ[F] s = 0 := hu.mul_left_inj.mp (by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hs, zero_mul])
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective
    exact hinj (hzero.trans (map_zero (Algebra.TensorProduct.includeRight : R →ₐ[F] E ⊗[F] R)).symm)

end Langlands.GroupScheme.KneserThree.QuatData
