import Langlands.GroupScheme.Quaternionic.Involution
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

/-! # Cancellation of a unit summand for `x ↦ x τ(x)` in `2 × 2` matrices -/

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Matrix

variable {F B : Type*} [CommRing F] [Ring B] [Algebra F B] (τ : FirstKindInvolution F B)

/-- The conjugate transpose of a `2 × 2` matrix in coordinates. -/
theorem matrix_fin_two (a b c d : B) :
    τ.matrix (Fin 2) !![a, b; c, d] = !![τ a, τ c; τ b, τ d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The matrix `Q = 1 - ᵗτ(u) λ u` satisfies `Q ᵗτ(Q) = 1` when
`λ + τ λ = λ (Σ uₖ τ uₖ) τ λ`. -/
theorem quasiReflection_mul (u : Fin 2 → B) (l : B)
    (hl : l + τ l = l * (u 0 * τ (u 0) + u 1 * τ (u 1)) * τ l) :
    !![1 - τ (u 0) * l * u 0, -(τ (u 0) * l * u 1); -(τ (u 1) * l * u 0), 1 - τ (u 1) * l * u 1] *
      τ.matrix (Fin 2)
        !![1 - τ (u 0) * l * u 0, -(τ (u 0) * l * u 1);
          -(τ (u 1) * l * u 0), 1 - τ (u 1) * l * u 1] = 1 := by
  set S := u 0 * τ (u 0) + u 1 * τ (u 1) with hS
  have key : ∀ i j : Fin 2, τ (u i) * (l + τ l - l * S * τ l) * u j = 0 := by
    intro i j
    rw [hl, sub_self, mul_zero, zero_mul]
  rw [one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, matrix_fin_two, mul_fin_two, of_apply,
      cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      FirstKindInvolution.map_sub, FirstKindInvolution.map_neg, FirstKindInvolution.map_one,
      FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply]
  · rw [← sub_eq_zero, ← neg_eq_zero, ← key 0 0, hS]; noncomm_ring
  · rw [← neg_eq_zero, ← key 0 1, hS]; noncomm_ring
  · rw [← neg_eq_zero, ← key 1 0, hS]; noncomm_ring
  · rw [← sub_eq_zero, ← neg_eq_zero, ← key 1 1, hS]; noncomm_ring

/-- **Cancellation of a unit summand.** If `diag(y, 1) = Z ᵗτ(Z)` for a `2 × 2` matrix `Z`
over `B`, and some central `μ` with `μ τ(μ) = 1` makes `μ - Z₁₁` a unit, then `y = a τ(a)`
for some `a`. -/
theorem exists_eq_mul_of_diag (y : B) (Z : Matrix (Fin 2) (Fin 2) B)
    (hZ : Z * τ.matrix (Fin 2) Z = !![y, 0; 0, 1]) (μ : B) (hμc : ∀ z, μ * z = z * μ)
    (hμ : μ * τ μ = 1) (hu : IsUnit (μ - Z 1 1)) : ∃ a : B, y = a * τ a := by
  obtain ⟨p, hp⟩ := hu
  set c := Z 1 0 with hc
  set d := Z 1 1 with hd
  have hτμ : τ μ * μ = 1 := by rw [← hμc]; exact hμ
  have hrow : c * τ c + d * τ d = 1 := by
    have := congrFun (congrFun hZ 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hc, hd] using this
  -- `β = (μ - d) τ μ` with inverse `λ = μ p⁻¹`.
  set l : B := μ * ↑p⁻¹ with hl
  set β : B := ↑p * τ μ with hβ
  have hβl : β * l = 1 := by
    rw [hβ, hl, mul_assoc, ← mul_assoc (τ μ), hτμ, one_mul, Units.mul_inv]
  have hlβ : l * β = 1 := by
    rw [hβ, hl, mul_assoc, ← mul_assoc (↑p⁻¹ : B), Units.inv_mul, one_mul, hμ]
  have hβval : β = 1 - d * τ μ := by
    rw [hβ, hp, sub_mul, hμ]
  let u : Fin 2 → B := ![c, d - μ]
  have hu0 : u 0 = c := rfl
  have hu1 : u 1 = d - μ := rfl
  have hβu : c * τ (u 0) + d * τ (u 1) = β := by
    rw [hu0, hu1, FirstKindInvolution.map_sub, mul_sub, ← add_sub_assoc, hrow, hβval]
  have hτβ : τ β = 1 - μ * τ d := by
    rw [hβval, FirstKindInvolution.map_sub, FirstKindInvolution.map_one,
      FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply]
  have huu : u 0 * τ (u 0) + u 1 * τ (u 1) = β + τ β := by
    rw [hu0, hu1, hτβ, hβval, FirstKindInvolution.map_sub]
    calc c * τ c + (d - μ) * (τ d - τ μ)
        = (c * τ c + d * τ d) - d * τ μ - μ * τ d + μ * τ μ := by noncomm_ring
      _ = 1 - d * τ μ + (1 - μ * τ d) := by rw [hrow, hμ]; noncomm_ring
  have hlτ : τ β * τ l = 1 := by
    rw [← FirstKindInvolution.map_mul, hlβ, FirstKindInvolution.map_one]
  have hkey : l + τ l = l * (u 0 * τ (u 0) + u 1 * τ (u 1)) * τ l := by
    rw [huu, mul_add, add_mul, hlβ, one_mul, mul_assoc l (τ β), hlτ, mul_one, add_comm]
  set Q := !![1 - τ (u 0) * l * u 0, -(τ (u 0) * l * u 1);
    -(τ (u 1) * l * u 0), 1 - τ (u 1) * l * u 1] with hQ
  have hQu : Q * τ.matrix (Fin 2) Q = 1 := quasiReflection_mul τ u l hkey
  set W := Z * Q with hW
  have hWW : W * τ.matrix (Fin 2) W = !![y, 0; 0, 1] := by
    rw [hW, FirstKindInvolution.map_mul, mul_assoc, ← mul_assoc Q, hQu, one_mul, hZ]
  have hW10 : W 1 0 = 0 := by
    have : W 1 0 = c * (1 - τ (u 0) * l * u 0) + d * (-(τ (u 1) * l * u 0)) := by
      simp [hW, hQ, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    rw [this, show c * (1 - τ (u 0) * l * u 0) + d * (-(τ (u 1) * l * u 0)) =
      c - (c * τ (u 0) + d * τ (u 1)) * l * u 0 by noncomm_ring, hβu, hβl, one_mul, hu0, sub_self]
  have hW11 : W 1 1 = μ := by
    have : W 1 1 = c * (-(τ (u 0) * l * u 1)) + d * (1 - τ (u 1) * l * u 1) := by
      simp [hW, hQ, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    rw [this, show c * (-(τ (u 0) * l * u 1)) + d * (1 - τ (u 1) * l * u 1) =
      d - (c * τ (u 0) + d * τ (u 1)) * l * u 1 by noncomm_ring, hβu, hβl, one_mul, hu1]
    abel
  have h01 : W 0 0 * τ (W 1 0) + W 0 1 * τ (W 1 1) = 0 := by
    have := congrFun (congrFun hWW 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h00 : W 0 0 * τ (W 0 0) + W 0 1 * τ (W 0 1) = y := by
    have := congrFun (congrFun hWW 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [hW10, hW11, FirstKindInvolution.map_zero, mul_zero, zero_add] at h01
  have hW01 : W 0 1 = 0 := by
    calc W 0 1 = W 0 1 * (τ μ * μ) := by rw [hτμ, mul_one]
      _ = 0 := by rw [← mul_assoc, h01, zero_mul]
  rw [hW01, FirstKindInvolution.map_zero, mul_zero, add_zero] at h00
  exact ⟨W 0 0, h00.symm⟩

end Langlands.CentralSimple.Landherr
