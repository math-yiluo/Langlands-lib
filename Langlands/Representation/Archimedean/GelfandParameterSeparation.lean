import Langlands.Representation.Archimedean.ComplexJacquetFinite
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Separation of normalized parameters by the Gelfand recursion

The sums of the diagonal values in the recursion determine the multiset
of parameters after the index shift.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.GelfandParameterSeparation

open ComplexJacquetFinite (gelPoly gelPoly_zero gelPoly_succ)
open scoped Polynomial

variable {n : ℕ}

/-- The value of a diagonal Gelfand polynomial at parameters with the index shift absorbed. -/
def value (b : Fin n → ℂ) (k : ℕ) (i : Fin n) : ℂ :=
  MvPolynomial.eval (fun a => b a - (a.val : ℂ)) (gelPoly n k i)

private theorem value_zero (b : Fin n → ℂ) (i : Fin n) : value b 0 i = 1 := by
  simp [value, gelPoly_zero]

private theorem value_succ (b : Fin n → ℂ) (k : ℕ) (i : Fin n) :
    value b (k + 1) i = b i * value b k i - ∑ j ∈ Finset.Iio i, value b k j := by
  simp [value, gelPoly_succ]

private def series (b : Fin n → ℂ) (i : Fin n) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => value b k i)

private def factor (b : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C b * PowerSeries.X

private theorem series_factor (b : Fin n → ℂ) (i : Fin n) :
    factor (b i) * series b i =
      1 - (∑ j ∈ Finset.Iio i, series b j) * PowerSeries.X := by
  rw [show factor (b i) * series b i =
      series b i - (series b i * PowerSeries.C (b i)) * PowerSeries.X from by
        unfold factor
        ring]
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_X,
      series, value_zero]
  | succ k =>
    have hstep (p : PowerSeries ℂ) :
        PowerSeries.coeff (k + 1) (p * PowerSeries.X) = PowerSeries.coeff k p := by
      simpa only [pow_one] using PowerSeries.coeff_mul_X_pow p 1 k
    simp only [map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false, hstep,
      PowerSeries.coeff_mul_C, map_sum, series, PowerSeries.coeff_mk, value_succ]
    ring

private theorem factor_succ (b : ℂ) : factor (b + 1) = factor b - PowerSeries.X := by
  simp only [factor, map_add, map_one]
  ring

private theorem series_product (b : Fin n → ℂ) (s : Finset (Fin n))
    (hs : ∀ a ∈ s, Finset.Iio a ⊆ s) :
    (1 - (∑ i ∈ s, series b i) * PowerSeries.X) * ∏ i ∈ s, factor (b i) =
      ∏ i ∈ s, factor (b i + 1) := by
  revert hs
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    intro hs
    have ha : a ∉ s := fun h => (lt_irrefl a) (hlt a h)
    have heq : Finset.Iio a = s := by
      ext i
      rw [Finset.mem_Iio]
      exact ⟨fun h =>
        (Finset.mem_insert.mp (hs a (Finset.mem_insert_self a s) (Finset.mem_Iio.mpr h))).resolve_left
          h.ne, fun h => hlt i h⟩
    have hs' : ∀ i ∈ s, Finset.Iio i ⊆ s := by
      intro i hi j hj
      rw [← heq, Finset.mem_Iio]
      exact (Finset.mem_Iio.mp hj).trans (hlt i hi)
    have hf := series_factor b a
    rw [heq] at hf
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    calc
      _ = ((1 - (∑ i ∈ s, series b i) * PowerSeries.X) * factor (b a) -
          (factor (b a) * series b a) * PowerSeries.X) * ∏ i ∈ s, factor (b i) := by ring
      _ = factor (b a + 1) *
          ((1 - (∑ i ∈ s, series b i) * PowerSeries.X) * ∏ i ∈ s, factor (b i)) := by
        rw [hf, factor_succ]
        ring
      _ = _ := by rw [ih hs']

private def reciprocal (b : Fin n → ℂ) : ℂ[X] :=
  ∏ i, (1 - Polynomial.C (b i) * Polynomial.X)

private def rootPolynomial (b : Fin n → ℂ) : ℂ[X] :=
  ∏ i, (Polynomial.X - Polynomial.C (b i))

private theorem reciprocal_toPowerSeries (b : Fin n → ℂ) :
    (reciprocal b : PowerSeries ℂ) = ∏ i, factor (b i) := by
  change Polynomial.coeToPowerSeries.ringHom (reciprocal b) = _
  simp [reciprocal, factor]

private theorem reciprocal_cross {b c : Fin n → ℂ}
    (h : ∀ k, ∑ i, value b k i = ∑ i, value c k i) :
    reciprocal (fun i => b i + 1) * reciprocal c =
      reciprocal (fun i => c i + 1) * reciprocal b := by
  have hs : ∑ i, series b i = ∑ i, series c i := by
    apply PowerSeries.ext
    intro k
    simpa only [map_sum, series, PowerSeries.coeff_mk] using h k
  have hb := series_product b Finset.univ (fun _ _ => Finset.subset_univ _)
  have hc := series_product c Finset.univ (fun _ _ => Finset.subset_univ _)
  rw [hs] at hb
  apply Polynomial.coe_injective ℂ
  simp only [Polynomial.coe_mul, reciprocal_toPowerSeries, ← hb, ← hc]
  ring

private theorem reciprocal_eval_mul (b : Fin n → ℂ) {z : ℂ} (hz : z ≠ 0) :
    (reciprocal b).eval z⁻¹ * z ^ n = (rootPolynomial b).eval z := by
  rw [show z ^ n = ∏ _i : Fin n, z by simp, reciprocal,
    rootPolynomial, Polynomial.eval_prod, Polynomial.eval_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hz,
    mul_one]

private theorem rootPolynomial_add_one_eval (b : Fin n → ℂ) (z : ℂ) :
    (rootPolynomial (fun i => b i + 1)).eval z = (rootPolynomial b).eval (z - 1) := by
  simp only [rootPolynomial, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  ring

private theorem rootPolynomial_cross {b c : Fin n → ℂ}
    (h : ∀ k, ∑ i, value b k i = ∑ i, value c k i) {z : ℂ} (hz : z ≠ 0) :
    (rootPolynomial b).eval (z - 1) * (rootPolynomial c).eval z =
      (rootPolynomial c).eval (z - 1) * (rootPolynomial b).eval z := by
  have he := congrArg (Polynomial.eval z⁻¹) (reciprocal_cross h)
  simp only [Polynomial.eval_mul] at he
  rw [← rootPolynomial_add_one_eval b, ← rootPolynomial_add_one_eval c]
  simp only [← reciprocal_eval_mul _ hz]
  calc
    _ = ((reciprocal (fun i => b i + 1)).eval z⁻¹ * (reciprocal c).eval z⁻¹) *
        (z ^ n * z ^ n) := by ring
    _ = _ := by rw [he]; ring

private theorem rootPolynomial_monic (b : Fin n → ℂ) : (rootPolynomial b).Monic :=
  Polynomial.monic_prod_X_sub_C _ _

private theorem rootPolynomial_eq_multiset_prod (b : Fin n → ℂ) :
    rootPolynomial b =
      ((Finset.univ : Finset (Fin n)).val.map b |>.map
        (fun z => Polynomial.X - Polynomial.C z)).prod := by
  simp only [rootPolynomial, ← Finset.prod_map_val, Multiset.map_map, Function.comp_def]

private theorem rootPolynomial_natDegree (b : Fin n → ℂ) :
    (rootPolynomial b).natDegree = n := by
  rw [rootPolynomial_eq_multiset_prod, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card,
    Multiset.card_map]
  simp

private theorem rootPolynomial_eq {b c : Fin n → ℂ}
    (h : ∀ k, ∑ i, value b k i = ∑ i, value c k i) :
    rootPolynomial b = rootPolynomial c := by
  let bound : ℝ := 1 + ∑ i, |(c i).re|
  let z (m : ℕ) : ℂ := (bound + (m : ℝ) : ℝ)
  have hpos (m : ℕ) : 0 < (z m).re := by
    have hsum : 0 ≤ ∑ i, |(c i).re| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    simp only [z, bound, Complex.ofReal_re]
    positivity
  have hne (m : ℕ) : z m ≠ 0 := fun e => by
    have hh := hpos m
    rw [e, Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  have hpc (m : ℕ) : (rootPolynomial c).eval (z m) ≠ 0 := by
    simp only [rootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (fun e => ?_)
    have hi : |(c i).re| ≤ ∑ j, |(c j).re| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (c j).re) (Finset.mem_univ i)
    have hmi : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hh := congrArg Complex.re e
    simp only [z, bound, Complex.ofReal_re] at hh
    linarith [le_abs_self (c i).re]
  let ratio : ℂ := (rootPolynomial b).eval (z 0) / (rootPolynomial c).eval (z 0)
  have he (m : ℕ) : (rootPolynomial b).eval (z m) = ratio * (rootPolynomial c).eval (z m) := by
    induction m with
    | zero => exact (div_mul_cancel₀ _ (hpc 0)).symm
    | succ m ih =>
      have hstep : z (m + 1) - 1 = z m := by
        simp only [z, Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_one]
        ring
      have hx := rootPolynomial_cross h (hne (m + 1))
      rw [hstep, ih] at hx
      apply mul_right_cancel₀ (hpc m)
      calc
        _ = (rootPolynomial c).eval (z m) * (rootPolynomial b).eval (z (m + 1)) := mul_comm _ _
        _ = (ratio * (rootPolynomial c).eval (z m)) *
            (rootPolynomial c).eval (z (m + 1)) := hx.symm
        _ = _ := by ring
  have hinj : Function.Injective z := by
    intro m k hmk
    have hmk' := congrArg Complex.re hmk
    simp only [z, Complex.ofReal_re, add_right_inj] at hmk'
    exact_mod_cast hmk'
  have hzero : rootPolynomial b - Polynomial.C ratio * rootPolynomial c = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (Set.infinite_range_of_injective hinj).mono ?_
    rintro _ ⟨m, rfl⟩
    simp [Polynomial.IsRoot, he m]
  have hpol := sub_eq_zero.mp hzero
  have hb : (rootPolynomial b).coeff n = 1 := by
    exact (congrArg (rootPolynomial b).coeff (rootPolynomial_natDegree b)).symm.trans
      (rootPolynomial_monic b).leadingCoeff
  have hc : (rootPolynomial c).coeff n = 1 := by
    exact (congrArg (rootPolynomial c).coeff (rootPolynomial_natDegree c)).symm.trans
      (rootPolynomial_monic c).leadingCoeff
  have hratio : ratio = 1 := by
    rw [hpol, Polynomial.coeff_C_mul, hc, mul_one] at hb
    exact hb
  simpa [hratio] using hpol

/-- Equal diagonal Gelfand traces give equal multisets of the shifted parameters. -/
theorem parameter_multiset_eq {b c : Fin n → ℂ}
    (h : ∀ k, ∑ i, value b k i = ∑ i, value c k i) :
    (Finset.univ : Finset (Fin n)).val.map b = (Finset.univ : Finset (Fin n)).val.map c := by
  have hroots (d : Fin n → ℂ) :
      (rootPolynomial d).roots = (Finset.univ : Finset (Fin n)).val.map d := by
    rw [rootPolynomial_eq_multiset_prod, Polynomial.roots_multiset_prod_X_sub_C]
  rw [← hroots b, ← hroots c, rootPolynomial_eq h]

end Langlands.Archimedean.GelfandParameterSeparation
