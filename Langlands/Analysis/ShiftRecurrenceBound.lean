import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Polynomial bounds for linear recurrences with roots in the closed unit disc

A complex sequence annihilated by `∏_{c ∈ w} (S - c)`, where `S` is the shift `u ↦ u(· + 1)` and
every root `c` satisfies `‖c‖ ≤ 1`, grows at most polynomially: `‖u q‖ ≤ 3^m (q + 1)^m M` with
`m = |w|` and `M` a nonnegative bound for the first `m` terms. The bound does not depend on the
roots. -/

noncomputable section

set_option autoImplicit false

open Polynomial

namespace Langlands.Analysis

/-- The shift `u ↦ (q ↦ u (q + 1))` on complex sequences. -/
def seqShift : Module.End ℂ (ℕ → ℂ) where
  toFun u q := u (q + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem seqShift_apply (u : ℕ → ℂ) (q : ℕ) : seqShift u q = u (q + 1) := rfl

theorem seqShift_pow_apply (i : ℕ) (u : ℕ → ℂ) (q : ℕ) : (seqShift ^ i) u q = u (q + i) := by
  induction i generalizing q with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, seqShift_apply, ih]
    ring_nf

/-- Evaluating a polynomial at the shift gives the corresponding linear combination of
shifted terms. -/
theorem aeval_seqShift_apply (D : ℂ[X]) (u : ℕ → ℂ) (q : ℕ) :
    aeval seqShift D u q = ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * u (q + k) := by
  rw [aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, seqShift_pow_apply]

/-- Along a sequence with `u (q + 1) = c u q + v q` and `‖c‖ ≤ 1`, the terms are bounded by
the first term plus the sum of the previous `v`'s. -/
theorem norm_le_add_sum_of_recurrence {c : ℂ} (hc : ‖c‖ ≤ 1) {u v : ℕ → ℂ}
    (huv : ∀ q, u (q + 1) = c * u q + v q) (q : ℕ) :
    ‖u q‖ ≤ ‖u 0‖ + ∑ p ∈ Finset.range q, ‖v p‖ := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [huv q, Finset.sum_range_succ]
    calc ‖c * u q + v q‖ ≤ ‖c‖ * ‖u q‖ + ‖v q‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ 1 * ‖u q‖ + ‖v q‖ := by gcongr
      _ ≤ _ := by linarith

/-- **Polynomial growth of linear recurrences with roots in the closed unit disc.** If the
product of the shifts `S - c`, `c ∈ w`, annihilates `u`, every root has `‖c‖ ≤ 1`, `M ≥ 0` and
`‖u j‖ ≤ M` for `j < |w|`, then `‖u q‖ ≤ 3^{|w|} (q + 1)^{|w|} M`. -/
theorem norm_le_of_aeval_seqShift_eq_zero (w : List ℂ) (hw : ∀ c ∈ w, ‖c‖ ≤ 1)
    (u : ℕ → ℂ) (hu : aeval seqShift (w.map fun c => X - C c).prod u = 0)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ j < w.length, ‖u j‖ ≤ M) (q : ℕ) :
    ‖u q‖ ≤ 3 ^ w.length * ((q : ℝ) + 1) ^ w.length * M := by
  induction w generalizing u M q with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one, Module.End.one_apply] at hu
    simp [hu, hM0]
  | cons c w ih =>
    have hc : ‖c‖ ≤ 1 := hw c List.mem_cons_self
    have hw' : ∀ c ∈ w, ‖c‖ ≤ 1 := fun c' h => hw c' (List.mem_cons_of_mem c h)
    set v : ℕ → ℂ := fun p => u (p + 1) - c * u p with hv
    have hu' : aeval seqShift ((X - C c) * (w.map fun c => X - C c).prod) u = 0 := by
      simpa only [List.map_cons, List.prod_cons] using hu
    have hvsol : aeval seqShift (w.map fun c => X - C c).prod v = 0 := by
      have h : v = aeval seqShift (X - C c) u := by
        funext p
        simp [hv, aeval_X, aeval_C, Module.algebraMap_end_apply]
      rw [h, ← Module.End.mul_apply, ← map_mul, mul_comm]
      exact hu'
    have hvM : ∀ j < w.length, ‖v j‖ ≤ 2 * M := by
      intro j hj
      have h1 : ‖u (j + 1)‖ ≤ M := hM (j + 1) (by simp; omega)
      have h2 : ‖u j‖ ≤ M := hM j (by simp; omega)
      calc ‖u (j + 1) - c * u j‖ ≤ ‖u (j + 1)‖ + ‖c‖ * ‖u j‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul]
        _ ≤ M + 1 * M := by gcongr
        _ = 2 * M := by ring
    have hvb := fun p => ih hw' v hvsol (2 * M) (by linarith) hvM p
    have hrec : ∀ p, u (p + 1) = c * u p + v p := fun p => by simp [hv]
    have h0 : ‖u 0‖ ≤ M := hM 0 (by simp)
    have key := norm_le_add_sum_of_recurrence hc hrec q
    have hsum : ∑ p ∈ Finset.range q, ‖v p‖ ≤
        (q : ℝ) * (3 ^ w.length * ((q : ℝ) + 1) ^ w.length * (2 * M)) := by
      have : ∀ p ∈ Finset.range q, ‖v p‖ ≤
          3 ^ w.length * ((q : ℝ) + 1) ^ w.length * (2 * M) := by
        intro p hp
        refine (hvb p).trans ?_
        have hpq : (p : ℝ) + 1 ≤ (q : ℝ) + 1 := by
          have := Finset.mem_range.mp hp
          have : (p : ℝ) ≤ q := by exact_mod_cast this.le
          linarith
        gcongr
      calc ∑ p ∈ Finset.range q, ‖v p‖ ≤
            ∑ _p ∈ Finset.range q, 3 ^ w.length * ((q : ℝ) + 1) ^ w.length * (2 * M) :=
            Finset.sum_le_sum this
        _ = _ := by simp
    have hq1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by have := q.cast_nonneg (α := ℝ); linarith
    have hpow1 : (1 : ℝ) ≤ 3 ^ w.length * ((q : ℝ) + 1) ^ w.length :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hq1)
    simp only [List.length_cons, pow_succ]
    have hA : 0 ≤ 3 ^ w.length * ((q : ℝ) + 1) ^ w.length := by positivity
    calc ‖u q‖ ≤ M + (q : ℝ) * (3 ^ w.length * ((q : ℝ) + 1) ^ w.length * (2 * M)) := by
          linarith
      _ ≤ (3 ^ w.length * ((q : ℝ) + 1) ^ w.length) * M +
            (3 ^ w.length * ((q : ℝ) + 1) ^ w.length) * (2 * (q : ℝ) * M) := by
          have : M ≤ (3 ^ w.length * ((q : ℝ) + 1) ^ w.length) * M := le_mul_of_one_le_left hM0 hpow1
          nlinarith
      _ = (3 ^ w.length * ((q : ℝ) + 1) ^ w.length) * ((1 + 2 * (q : ℝ)) * M) := by ring
      _ ≤ (3 ^ w.length * ((q : ℝ) + 1) ^ w.length) * ((3 * ((q : ℝ) + 1)) * M) := by
          gcongr
          linarith
      _ = _ := by ring

/-- Rescaling a sequence by `κ^{-q}` divides the roots of an annihilating product by `κ`. -/
theorem aeval_seqShift_scaled {κ : ℂ} (hκ : κ ≠ 0) (w : List ℂ) (v : ℕ → ℂ) :
    aeval seqShift ((w.map fun c => X - C (c / κ)).prod) (fun q => v q / κ ^ q) =
      fun q => aeval seqShift ((w.map fun c => X - C c).prod) v q / κ ^ (q + w.length) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih]
    funext q
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Pi.sub_apply, seqShift_apply,
      List.length_cons, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : κ ^ (q + 1 + w.length) = κ ^ (q + (w.length + 1)) := by ring_nf
    rw [h1]
    field_simp
    ring

/-- **Polynomial growth along a translation equation.** Let `a` be an element of a monoid and
`φ` a complex function with `∑_k c_k φ(a^k g) = 0` for every `g`, where
`∏_{k < m} (X - w_k) = ∑_k c_k X^k` and `‖w_k‖ ≤ κ` with `κ > 0`. If `M ≥ 0` and
`‖φ(a^j g)‖ ≤ κ^j M` for `j < m`, then `‖φ(a^q g)‖ ≤ 3^m (q + 1)^m κ^q M` for every `q`. -/
theorem norm_le_of_translationSolution {A : Type*} [Monoid A] (a : A) {m : ℕ} (w : Fin m → ℂ)
    {κ : ℝ} (hκ : 0 < κ) (hw : ∀ k, ‖w k‖ ≤ κ) (φ : A → ℂ)
    (hφ : ∀ g, ∑ k ∈ Finset.range ((∏ k, (X - C (w k))).natDegree + 1),
      (∏ k, (X - C (w k))).coeff k * φ (a ^ k * g) = 0)
    (g : A) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j < m, ‖φ (a ^ j * g)‖ ≤ κ ^ j * M) (q : ℕ) :
    ‖φ (a ^ q * g)‖ ≤ 3 ^ m * ((q : ℝ) + 1) ^ m * κ ^ q * M := by
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  set v : ℕ → ℂ := fun q => φ (a ^ q * g) with hv
  have hprod : (∏ k, (X - C (w k)) : ℂ[X]) = ((List.ofFn w).map fun c => X - C c).prod := by
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  have hvsol : aeval seqShift ((List.ofFn w).map fun c => X - C c).prod v = 0 := by
    funext p
    rw [aeval_seqShift_apply, ← hprod, Pi.zero_apply]
    have := hφ (a ^ p * g)
    simpa only [hv, pow_add, mul_assoc, ← mul_assoc (a ^ p), add_comm p] using
      (by simpa only [← mul_assoc, ← pow_add, add_comm] using this)
  set u : ℕ → ℂ := fun q => v q / (κ : ℂ) ^ q with hu
  have husol : aeval seqShift (((List.ofFn w).map fun c => c / (κ : ℂ)).map
      fun c => X - C c).prod u = 0 := by
    rw [List.map_map]
    have h := aeval_seqShift_scaled hκC (List.ofFn w) v
    simp only [Function.comp_def] at h ⊢
    rw [h]
    funext p
    simp only [hvsol, Pi.zero_apply, zero_div]
  have hroots : ∀ c ∈ (List.ofFn w).map fun c => c / (κ : ℂ), ‖c‖ ≤ 1 := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc'
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    exact (div_le_one hκ).mpr (hw k)
  have hlen : ((List.ofFn w).map fun c => c / (κ : ℂ)).length = m := by simp
  have hum : ∀ j < ((List.ofFn w).map fun c => c / (κ : ℂ)).length, ‖u j‖ ≤ M := by
    intro j hj
    rw [hlen] at hj
    have hpos : 0 < κ ^ j := pow_pos hκ j
    simp only [hu, hv, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    rw [div_le_iff₀ hpos, mul_comm]
    exact hM j hj
  have hb := norm_le_of_aeval_seqShift_eq_zero _ hroots u husol M hM0 hum q
  rw [hlen] at hb
  have hpos : 0 < κ ^ q := pow_pos hκ q
  have hvq : φ (a ^ q * g) = u q * (κ : ℂ) ^ q := by
    simp only [hu, hv]
    field_simp
  rw [hvq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  calc ‖u q‖ * κ ^ q ≤ (3 ^ m * ((q : ℝ) + 1) ^ m * M) * κ ^ q := by gcongr
    _ = _ := by ring

end Langlands.Analysis
