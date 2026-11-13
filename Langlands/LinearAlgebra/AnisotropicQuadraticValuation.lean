import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Henselian

/-! # The valuation inequality for anisotropic quadratic forms -/

noncomputable section

universe u v

namespace Langlands.AnisotropicQuadratic

open Polynomial IsLocalRing

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {V : Type v} [AddCommGroup V] [Module K V]

local notation "ν" => (NormedField.valuation (K := K))

/-- The polar pairing is bounded by the geometric mean of the quadratic values. -/
theorem polar_norm_sq_le [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]
    (Q : QuadraticForm K V) (hQ : Q.Anisotropic) (x y : V) :
    ‖QuadraticMap.polar Q x y‖ ^ 2 ≤ ‖Q x‖ * ‖Q y‖ := by
  by_contra h
  have hlt : ‖Q x‖ * ‖Q y‖ < ‖QuadraticMap.polar Q x y‖ ^ 2 := lt_of_not_ge h
  set a := Q x
  set b := QuadraticMap.polar Q x y
  set c := Q y
  have hb : b ≠ 0 := by
    intro hb
    change ‖a‖ * ‖c‖ < ‖b‖ ^ 2 at hlt
    simp only [hb, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hlt
    exact (mul_nonneg (norm_nonneg _) (norm_nonneg _)).not_gt hlt
  have ha : a ≠ 0 := by
    intro ha
    have hx : x = 0 := hQ x ha
    exact hb (by simp [b, hx])
  let d : K := a * c / b ^ 2
  have hd : ‖d‖ < 1 := by
    dsimp [d]
    rw [norm_div, norm_mul, norm_pow]
    exact (div_lt_one (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hb))).mpr hlt
  have hvd : ν d < 1 := by
    change ‖d‖₊ < 1
    exact_mod_cast hd
  let d₀ : (NormedField.valuation (K := K)).valuationSubring := ⟨d, hvd.le⟩
  let f : Polynomial (NormedField.valuation (K := K)).valuationSubring := X ^ 2 + X + C d₀
  have hfm : f.Monic := by
    dsimp [f]
    rw [add_assoc]
    apply monic_X_pow_add
    apply lt_of_le_of_lt (degree_add_le _ _)
    exact max_lt (by simp) (lt_of_le_of_lt degree_C_le (by norm_num))
  have hf0 : f.eval 0 ∈ maximalIdeal (NormedField.valuation (K := K)).valuationSubring := by
    change (X ^ 2 + X + C d₀).eval 0 ∈ _
    simp only [eval_add, eval_pow, eval_X, eval_C, zero_pow (by decide : 2 ≠ 0),
      zero_add]
    exact (Valuation.mem_maximalIdeal_iff (v := NormedField.valuation (K := K))).mpr hvd
  have hfd : IsUnit (f.derivative.eval 0) := by
    simpa only [f, derivative_add, derivative_pow, derivative_X, derivative_C,
      eval_add, eval_mul, eval_natCast, eval_pow, eval_X, eval_one, eval_zero,
      zero_pow (by decide : 1 ≠ 0), mul_zero, zero_mul, add_zero, zero_add] using
      (isUnit_one : IsUnit (1 : (NormedField.valuation (K := K)).valuationSubring))
  obtain ⟨z, hz, -⟩ := HenselianLocalRing.is_henselian f hfm 0 hf0 hfd
  have hz' : (z : K) ^ 2 + (z : K) + d = 0 := by
    have hz₀ : z ^ 2 + z + d₀ = 0 := by simpa [f, IsRoot] using hz
    simpa [d₀] using congrArg (fun w : (NormedField.valuation (K := K)).valuationSubring =>
      (w : K)) hz₀
  let t : K := b * (z : K) / a
  have hroot : Q (t • x + y) = 0 := by
    have he : a * t ^ 2 + b * t + c = 0 := by
      dsimp [t]
      dsimp [d] at hz'
      field_simp at hz' ⊢
      linear_combination hz'
    rw [QuadraticMap.map_add Q, Q.map_smul, QuadraticMap.polar_smul_left]
    simp only [smul_eq_mul]
    change t * t * a + c + t * b = 0
    linear_combination he
  have hy : y = -t • x := by
    have hr := hQ _ hroot
    exact (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hr)).trans
      (neg_smul t x).symm
  have hc : c = t ^ 2 * a := by
    simp [c, hy, Q.map_smul, smul_eq_mul, pow_two, a]
  have hbe : b = -t * (2 * a) := by
    simp [b, hy, QuadraticMap.polar_self, smul_eq_mul, a]
  have htwo : ‖(2 : K)‖ ≤ 1 := by
    simpa only [← one_add_one_eq_two, norm_one, max_self] using
      (IsUltrametricDist.norm_add_le_max (1 : K) 1)
  have htwo0 := norm_nonneg (2 : K)
  have ht0 := norm_nonneg t
  have ha0 := norm_nonneg a
  have htwo2 : ‖(2 : K)‖ ^ 2 ≤ 1 := by nlinarith
  have hbound : ‖b‖ ^ 2 ≤ ‖a‖ * ‖c‖ := by
    rw [hbe, hc, norm_mul, norm_mul, norm_neg, norm_mul, norm_pow]
    nlinarith [mul_nonneg (sq_nonneg ‖t‖) (sq_nonneg ‖a‖),
      mul_nonneg (sub_nonneg.mpr htwo2) (mul_nonneg (sq_nonneg ‖t‖) (sq_nonneg ‖a‖))]
  exact (not_le_of_gt hlt) hbound


/-- The polar pairing satisfies the corresponding maximum bound. -/
theorem polar_norm_le_max [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]
    (Q : QuadraticForm K V) (hQ : Q.Anisotropic) (x y : V) :
    ‖QuadraticMap.polar Q x y‖ ≤ max ‖Q x‖ ‖Q y‖ := by
  have hs := polar_norm_sq_le Q hQ x y
  have hm : ‖Q x‖ * ‖Q y‖ ≤ (max ‖Q x‖ ‖Q y‖) ^ 2 := by
    simpa only [pow_two] using mul_le_mul (le_max_left ‖Q x‖ ‖Q y‖)
      (le_max_right ‖Q x‖ ‖Q y‖) (norm_nonneg _) (le_trans (norm_nonneg _) (le_max_left _ _))
  have hp := norm_nonneg (QuadraticMap.polar Q x y)
  have hn : 0 ≤ max ‖Q x‖ ‖Q y‖ := le_trans (norm_nonneg _) (le_max_left _ _)
  nlinarith

/-- An anisotropic quadratic form over a Henselian ultrametric field obeys the
ultrametric triangle inequality on its values. -/
theorem norm_map_add_le_max
    [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]
    (Q : QuadraticForm K V) (hQ : Q.Anisotropic) (x y : V) :
    ‖Q (x + y)‖ ≤ max ‖Q x‖ ‖Q y‖ := by
  rw [QuadraticMap.map_add Q]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (IsUltrametricDist.norm_add_le_max _ _) (polar_norm_le_max Q hQ x y))


local instance valuationRingModule :
    Module (NormedField.valuation (K := K)).valuationSubring V :=
  Module.compHom V (NormedField.valuation (K := K)).valuationSubring.subtype

/-- A nonnegative sublevel set of an anisotropic quadratic form is a module over
the valuation ring. These are the lattices used to define the residue forms. -/
def valueLattice
    [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]
    (Q : QuadraticForm K V) (hQ : Q.Anisotropic) (r : ℝ) (hr : 0 ≤ r) :
    Submodule (NormedField.valuation (K := K)).valuationSubring V where
  carrier := {x | ‖Q x‖ ≤ r}
  zero_mem' := by simpa using hr
  add_mem' hx hy := (norm_map_add_le_max Q hQ _ _).trans (max_le hx hy)
  smul_mem' c x hx := by
    change ‖Q ((c : K) • x)‖ ≤ r
    have hc : ‖(c : K)‖ ≤ 1 := by
      exact_mod_cast c.prop
    have hc0 := norm_nonneg (c : K)
    have hc2 : ‖(c : K)‖ ^ 2 ≤ 1 := by nlinarith
    calc
      ‖Q ((c : K) • x)‖ = ‖(c : K)‖ ^ 2 * ‖Q x‖ := by
        simp [Q.map_smul, smul_eq_mul, pow_two, norm_mul]
      _ ≤ 1 * ‖Q x‖ := mul_le_mul_of_nonneg_right hc2 (norm_nonneg _)
      _ ≤ r := by simpa using hx

@[simp]
theorem mem_valueLattice
    [HenselianLocalRing (NormedField.valuation (K := K)).valuationSubring]
    (Q : QuadraticForm K V) (hQ : Q.Anisotropic) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    x ∈ valueLattice Q hQ r hr ↔ ‖Q x‖ ≤ r := Iff.rfl

end Langlands.AnisotropicQuadratic
