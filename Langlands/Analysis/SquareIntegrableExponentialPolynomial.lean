import Langlands.Analysis.BoundedExponentialPolynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Polynomial

/-! # Nondecaying exponents in a square-integrable exponential polynomial -/

noncomputable section

open Filter MeasureTheory Polynomial Set
open scoped Topology ENNReal

set_option autoImplicit false

namespace Langlands.Analysis

universe u

private abbrev rayMeasure : Measure ℝ := volume.restrict (Ici 0)

private theorem memLp_translate_ray (h : ℝ) (hh : 0 ≤ h) {f : ℝ → ℂ}
    (hf : MemLp f 2 rayMeasure) : MemLp (fun t => f (t + h)) 2 rayMeasure := by
  have hm : (volume : Measure ℝ).restrict (Ici h) ≤ rayMeasure :=
    Measure.restrict_mono (Ici_subset_Ici.mpr hh) le_rfl
  have hmp := (measurePreserving_add_right (volume : Measure ℝ) h).restrict_preimage (measurableSet_Ici (a := h))
  have he : (fun t => t + h) ⁻¹' Ici h = Ici 0 := by
    ext t
    simp
  rw [he] at hmp
  exact (hf.mono_measure hm).comp_measurePreserving hmp

private theorem not_memLp_single_exp {z : ℂ} (hz : 0 ≤ z.re) {q : ℂ[X]} (hq : q ≠ 0) :
    ¬ MemLp (fun t : ℝ => Complex.exp (t * z) * q.eval (t : ℂ)) 2 rayMeasure := by
  intro h
  have hpoly : ∃ a c : ℝ, 0 ≤ a ∧ 0 < c ∧ ∀ t ≥ a, c ≤ ‖q.eval (t : ℂ)‖ := by
    by_cases hd : 0 < q.degree
    · have hx : Tendsto (fun t : ℝ => ‖(t : ℂ)‖) atTop atTop := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        exact tendsto_atTop_mono (fun _ => le_abs_self _) tendsto_id
      obtain ⟨A, hA⟩ := eventually_atTop.mp ((tendsto_atTop.mp (q.tendsto_norm_atTop hd hx)) 1)
      exact ⟨max A 0, 1, le_max_right _ _, zero_lt_one, fun t ht => hA t ((le_max_left _ _).trans ht)⟩
    · have hC := eq_C_of_degree_le_zero (le_of_not_gt hd)
      have hn : q.coeff 0 ≠ 0 := fun he => hq (by rw [hC, he, C_0])
      refine ⟨0, ‖q.coeff 0‖, le_rfl, norm_pos_iff.mpr hn, fun t _ => ?_⟩
      have he : q.eval (t : ℂ) = q.coeff 0 := by conv_lhs => rw [hC, eval_C]
      rw [he]
  obtain ⟨a, c, ha, hc, hpoly⟩ := hpoly
  let μ : Measure ℝ := volume.restrict (Ici a)
  have hμ : μ ≤ rayMeasure := Measure.restrict_mono (Ici_subset_Ici.mpr ha) le_rfl
  have hconst : MemLp (fun _ : ℝ => c) 2 μ := by
    refine (h.mono_measure hμ).mono aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ici a) measurableSet_Ici] with t ht
    rw [Real.norm_of_nonneg hc.le, norm_mul, Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact (hpoly t ht).trans (le_mul_of_one_le_left (norm_nonneg _)
      ((Real.one_le_exp_iff).mpr (mul_nonneg (ha.trans ht) hz)))
  have hfalse := (memLp_const_iff (μ := μ) (p := 2) (c := c) (by norm_num) (by simp)).mp hconst
  rcases hfalse with hzero | hfinite
  · exact hc.ne' hzero
  · simp [μ, Real.volume_Ici] at hfinite

private theorem exists_distinct_exponential_step {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : InjOn z (s : Set ι)) :
    ∃ h > (0 : ℝ), InjOn (fun j => Complex.exp ((h : ℂ) * z j)) (s : Set ι) := by
  let A := ∑ j ∈ s, |(z j).im|
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let h := Real.pi / (A + 1)
  have hh : 0 < h := div_pos Real.pi_pos (by linarith)
  refine ⟨h, hh, fun i hi j hj hEq => hz hi hj ?_⟩
  have hb (k : ι) (hk : k ∈ s) : |(((h : ℝ) : ℂ) * z k).im| < Real.pi := by
    have hle : |(z k).im| ≤ A := Finset.single_le_sum (f := fun j => |(z j).im|)
      (fun j _ => abs_nonneg _) hk
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul, abs_of_pos hh]
    dsimp only [h]
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ (by linarith : 0 < A + 1)).mpr
      (mul_lt_mul_of_pos_left (by linarith) Real.pi_pos)
  have hi' := abs_lt.mp (hb i hi)
  have hj' := abs_lt.mp (hb j hj)
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hh.ne')
    (Complex.exp_inj_of_neg_pi_lt_of_le_pi hi'.1 hi'.2.le hj'.1 hj'.2.le hEq)

private def degreeCount (q : ℂ[X]) : ℕ := if q = 0 then 0 else q.natDegree + 1

private theorem degreeCount_difference_le (a b r : ℂ) (q : ℂ[X]) :
    degreeCount (C a * taylor r q - C b * q) ≤ degreeCount q := by
  by_cases hq : q = 0
  · simp [hq, degreeCount]
  · by_cases hz : C a * taylor r q - C b * q = 0
    · simp [degreeCount, hz]
    · have hd := natDegree_sub_le (C a * taylor r q) (C b * q)
      have ha := (natDegree_C_mul_le a (taylor r q)).trans (natDegree_taylor q r).le
      have hb := natDegree_C_mul_le b q
      simp [degreeCount, hq, hz]
      omega

private theorem degreeCount_difference_lt (a r : ℂ) {q : ℂ[X]} (hq : q ≠ 0) :
    degreeCount (C a * taylor r q - C a * q) < degreeCount q := by
  by_cases hz : C a * taylor r q - C a * q = 0
  · simp [degreeCount, hz, hq]
  · have hdiff : taylor r q - q ≠ 0 := fun he => hz (by rw [← mul_sub, he, mul_zero])
    have hdeg := degree_sub_lt_left (degree_taylor q r) ((taylor_eq_zero r q).not.mpr hq)
      (leadingCoeff_taylor r q)
    have hlt := (natDegree_lt_natDegree hdiff hdeg).trans_eq (natDegree_taylor q r)
    have hle := natDegree_C_mul_le a (taylor r q - q)
    have h := show (C a * taylor r q - C a * q).natDegree < q.natDegree by
      rw [← mul_sub]
      exact hle.trans_lt hlt
    simp [degreeCount, hz, hq]
    omega

private theorem difference_ne_zero {a b r : ℂ} (hab : a ≠ b) {q : ℂ[X]} (hq : q ≠ 0) :
    C a * taylor r q - C b * q ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℂ[X] => p.coeff q.natDegree) h
  simp only [coeff_sub, coeff_C_mul, coeff_taylor_natDegree, coeff_natDegree, coeff_zero, ← sub_mul] at hc
  exact (mul_ne_zero (sub_ne_zero.mpr hab) (leadingCoeff_ne_zero.mpr hq)) hc

/-- In a finite exponential polynomial with distinct exponents, square integrability on the
positive real ray forces the polynomial at each exponent of nonnegative real part to vanish. -/
def SquareIntegrableExponentialPolynomialStatement : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (z : ι → ℂ), InjOn z (s : Set ι) →
    ∀ q : ι → ℂ[X], MemLp (expPolynomial s z q) 2 (volume.restrict (Ici 0)) →
      ∀ i ∈ s, 0 ≤ (z i).re → q i = 0

/-- A positive shift with distinct multipliers reduces the total degree count while preserving
square integrability and keeping any chosen nondecaying term. Iterate until only that term
survives and use its positive lower bound on a tail. -/
theorem squareIntegrableExponentialPolynomial : SquareIntegrableExponentialPolynomialStatement := by
  classical
  intro ι s z hz p hp i hi hre
  obtain ⟨h, hh, hsep⟩ := exists_distinct_exponential_step s z hz
  suffices hind : ∀ m : ℕ, ∀ q : ι → ℂ[X], (∑ j ∈ s, degreeCount (q j)) = m →
      MemLp (expPolynomial s z q) 2 rayMeasure → q i = 0 from hind _ p rfl hp
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro q hm hq
    by_contra hqi
    by_cases hdiff : ∃ j ∈ s, j ≠ i ∧ q j ≠ 0
    · obtain ⟨j, hj, hji, hqj⟩ := hdiff
      let a (k : ι) := Complex.exp ((h : ℂ) * z k)
      let q' (k : ι) := C (a k) * taylor (h : ℂ) (q k) - C (a j) * q k
      have hdecomp (t : ℝ) : expPolynomial s z q' t =
          expPolynomial s z q (t + h) - a j * expPolynomial s z q t := by
        unfold expPolynomial
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [q', a, eval_sub, eval_mul, eval_C, taylor_eval, Complex.ofReal_add,
          add_mul, Complex.exp_add]
        ring
      have hint : MemLp (expPolynomial s z q') 2 rayMeasure := by
        have hshift := (memLp_translate_ray h hh.le hq).sub (hq.const_mul (a j))
        convert hshift using 1
        funext t
        exact hdecomp t
      have hlt : (∑ k ∈ s, degreeCount (q' k)) < m := by
        rw [← hm]
        exact Finset.sum_lt_sum (fun k _ => degreeCount_difference_le _ _ _ _)
          ⟨j, hj, degreeCount_difference_lt _ _ hqj⟩
      have hne : a i ≠ a j := fun he => hji ((hsep hi hj he).symm)
      exact difference_ne_zero hne hqi (ih _ hlt q' rfl hint)
    · have hterm (t : ℝ) : expPolynomial s z q t = Complex.exp (t * z i) * (q i).eval (t : ℂ) := by
        unfold expPolynomial
        apply Finset.sum_eq_single_of_mem i hi
        intro j hj hji
        have hzero : q j = 0 := by_contra fun hj0 => hdiff ⟨j, hj, hji, hj0⟩
        simp only [hzero, eval_zero, mul_zero]
      exact not_memLp_single_exp hre hqi (by rwa [← funext hterm])

end Langlands.Analysis
