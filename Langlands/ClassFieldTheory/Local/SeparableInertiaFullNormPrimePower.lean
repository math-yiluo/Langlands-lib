import Langlands.ClassFieldTheory.Local.SeparableInertiaNormAmbient
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Full norm surjectivity for prime-power Galois groups -/

noncomputable section

open Module
open scoped NNReal

namespace Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

namespace CyclicHyp

variable {B C : Type*} [Field B] [Field C] [Algebra B C]
  [FiniteDimensional B C] [IsGalois B C]
  {w : Valuation C ℝ≥0} {π : B} (h : CyclicHyp w π)

include h

/-- Total ramification and valuation-one norm surjectivity imply full norm surjectivity. -/
theorem surjective_norm : Function.Surjective (Algebra.norm B : C → B) := by
  obtain ⟨πL, hπL⟩ := h.exists_val_pow_eq
  have hvN : w (algebraMap B C (Algebra.norm B πL)) = w (algebraMap B C π) := by
    rw [h.val_norm, hπL]
  have hN0 : Algebra.norm B πL ≠ 0 := by
    intro h0
    have := h.gamma_pos
    rw [← hvN, h0, map_zero, map_zero] at this
    exact lt_irrefl _ this
  have hint : ∀ u : B, u ≠ 0 → w (algebraMap B C u) ≤ 1 →
      ∃ x : C, Algebra.norm B x = u := by
    intro u hu0 hu
    obtain ⟨k, hk⟩ := h.val_eq_pow hu0 hu
    have hquot : w (algebraMap B C (u / Algebra.norm B πL ^ k)) = 1 := by
      rw [map_div₀, map_div₀, map_pow, map_pow, hvN, hk,
        div_self (pow_ne_zero k h.gamma_pos.ne')]
    obtain ⟨x, -, hx⟩ := h.exists_norm_eq (u / Algebra.norm B πL ^ k) hquot
    refine ⟨x * πL ^ k, ?_⟩
    rw [map_mul, map_pow, hx, div_mul_cancel₀ _ (pow_ne_zero k hN0)]
  intro u
  rcases eq_or_ne u 0 with rfl | hu0
  · exact ⟨0, Algebra.norm_zero⟩
  by_cases hu : w (algebraMap B C u) ≤ 1
  · exact hint u hu0 hu
  · have huinv : w (algebraMap B C u⁻¹) ≤ 1 := by
      rw [map_inv₀, map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_not_ge hu)
    obtain ⟨x, hx⟩ := hint u⁻¹ (inv_ne_zero hu0) huinv
    exact ⟨x⁻¹, by rw [Algebra.norm_inv, hx, inv_inv]⟩

end CyclicHyp

namespace ReductionHyp

variable {E M : Type*} [Field E] [Field M] [Algebra E M]
  [FiniteDimensional E M] [IsGalois E M]
  {w : Valuation M ℝ≥0} {p : ℕ} (h : ReductionHyp (E := E) w p)

include h

/-- The full norm in every Galois prime-degree subextension is surjective. -/
theorem surjective_norm_cyclic (B : IntermediateField E M) (C : IntermediateField B M)
    [IsGalois B C] (hq : (finrank B C).Prime) :
    Function.Surjective (Algebra.norm B : C → B) := by
  obtain ⟨π, hπ⟩ := h.unif_of B
  have hc : CyclicHyp (w.comap (algebraMap C M)) π :=
    cyclicHyp_of_tower (h.inv_of B) hq (h.hensel_of B) (h.residueRoot_of B) hπ (h.res_of B)
  exact hc.surjective_norm

/-- Prime-power Galois groups have surjective full norms, for every prime `q`. -/
theorem surjective_norm_pgroup {q : ℕ} (hq : q.Prime) (k : ℕ) :
    ∀ B : IntermediateField E M, finrank B M = q ^ k →
      Function.Surjective (Algebra.norm B : M → B) := by
  have : Fact q.Prime := ⟨hq⟩
  induction k with
  | zero =>
    intro B hB u
    refine ⟨algebraMap B M u, ?_⟩
    rw [Algebra.norm_algebraMap, hB, pow_zero, pow_one]
  | succ k ih =>
    intro B hB u
    have hcard : Nat.card Gal(M/B) = q ^ (k + 1) := by
      rw [IsGalois.card_aut_eq_finrank, hB]
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime q (n := k)
      (by rw [hcard]; exact pow_dvd_pow q (Nat.le_succ k))
    have hidx : H.index = q := by
      have := H.card_mul_index
      rw [hH, hcard, pow_succ] at this
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos k) this
    have hnormal : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by
      rw [hidx, hcard, Nat.pow_minFac (by omega), hq.minFac_eq])
    set C := IntermediateField.fixedField H
    have hCM : finrank C M = q ^ k := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH]
    have hBC : finrank B C = q := by
      have := Module.finrank_mul_finrank B C M
      rw [hCM, hB, pow_succ, mul_comm] at this
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos k) this
    obtain ⟨x, hxN⟩ := h.surjective_norm_cyclic B C (hBC ▸ hq) u
    set C' : IntermediateField E M := C.restrictScalars E
    obtain ⟨z, hzN⟩ := ih C' hCM ⟨x, x.2⟩
    refine ⟨z, ?_⟩
    have hzC : Algebra.norm C z = x := by
      let e : C' ≃+* C :=
        { toFun := fun y => ⟨y.1, y.2⟩
          invFun := fun y => ⟨y.1, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl }
      rw [← Algebra.norm_eq_of_ringEquiv e (by ext; rfl), hzN]
      rfl
    rw [← Algebra.norm_norm (S := C), hzC, hxN]

/-- A chosen preimage for the full norm in a prime-power Galois subextension. -/
def normSection_pgroup {q : ℕ} (hq : q.Prime) (k : ℕ)
    (B : IntermediateField E M) (hBM : finrank B M = q ^ k) : B → M :=
  fun u => Classical.choose (h.surjective_norm_pgroup hq k B hBM u)

/-- The chosen preimage function is a right inverse of the determinant norm. -/
theorem norm_normSection_pgroup {q : ℕ} (hq : q.Prime) (k : ℕ)
    (B : IntermediateField E M) (hBM : finrank B M = q ^ k) (u : B) :
    Algebra.norm B (h.normSection_pgroup hq k B hBM u) = u :=
  Classical.choose_spec (h.surjective_norm_pgroup hq k B hBM u)

end ReductionHyp

end Langlands.ClassFieldTheory.Local.SeparableInertiaNorm
