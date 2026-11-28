import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic

/-! # Uniqueness of power series coefficients and polynomial functions

Two complex power series that converge to the same value at every nonzero point of a small
disc have the same coefficients. A function on `ℂˣ` that is given by a polynomial is determined
by its values on any infinite set; finite sums and products of polynomial functions and
evaluations of multivariate polynomials at polynomial coordinates are polynomial. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Filter Topology
open scoped ENNReal NNReal

section PowerSeries

/-- **A power series vanishing on a punctured disc is zero.** -/
theorem eq_zero_of_hasSum_pow {d : ℕ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z : ℂ, z ≠ 0 → ‖z‖ < ρ → HasSum (fun n => d n * z ^ n) 0) : d = 0 := by
  set p := FormalMultilinearSeries.ofScalars ℂ d with hp
  set f : ℂ → ℂ := fun z => ∑' n, d n * z ^ n with hf
  set ρ' : NNReal := ⟨ρ / 2, by positivity⟩ with hρ'
  have hρ'pos : (0 : ℝ) < ρ' := by
    change 0 < ρ / 2
    positivity
  have hρ'lt : (ρ' : ℝ) < ρ := by
    change ρ / 2 < ρ
    linarith
  have hrad : (ρ' : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_tendsto (l := 0)
    have hs := (h (ρ' : ℂ) (by exact_mod_cast hρ'pos.ne') (by
      rw [Complex.norm_real, Real.norm_of_nonneg hρ'pos.le]
      exact hρ'lt)).summable
    have ht := hs.tendsto_atTop_zero.norm
    rw [norm_zero] at ht
    refine ht.congr fun n => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hρ'pos.le]
  have hser : HasFPowerSeriesOnBall f p 0 ρ' := by
    refine ⟨hrad, by exact_mod_cast hρ'pos, fun {y} hy => ?_⟩
    rw [zero_add]
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    by_cases hy0 : y = 0
    · subst hy0
      have h0 : HasSum (fun n => d n * (0 : ℂ) ^ n) (d 0) := by
        convert hasSum_ite_eq 0 (d 0) using 1
        funext n
        cases n <;> simp
      rw [hf]
      simp only
      rw [h0.tsum_eq]
      exact h0
    · have hy' : ‖y‖ < ρ := by
        have hy1 : y ∈ Metric.ball (0 : ℂ) (ρ' : ℝ) := by
          rw [← Metric.eball_coe]
          exact hy
        rw [Metric.mem_ball, dist_zero_right] at hy1
        linarith
      have h1 := h y hy0 hy'
      rw [hf]
      simp only
      rw [h1.tsum_eq]
      exact h1
  by_contra hne
  have hp0 : p ≠ 0 := fun h0 => hne ((FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).1 h0)
  have hev := hser.hasFPowerSeriesAt.locally_ne_zero hp0
  have hsmall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z‖ < ρ :=
    nhdsWithin_le_nhds (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with z hz
      rwa [Metric.mem_ball, dist_zero_right] at hz)
  obtain ⟨z, hz1, hz2, hz3⟩ := (hev.and (hsmall.and self_mem_nhdsWithin)).exists
  exact hz1 (h z hz3 hz2).tsum_eq

/-- **Uniqueness of power series coefficients.** -/
theorem eq_of_hasSum_pow {c c' : ℕ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z : ℂ, z ≠ 0 → ‖z‖ < ρ →
      ∃ F, HasSum (fun n => c n * z ^ n) F ∧ HasSum (fun n => c' n * z ^ n) F) : c = c' := by
  have h0 := eq_zero_of_hasSum_pow (d := c - c') hρ fun z hz hzρ => by
    obtain ⟨F, h1, h2⟩ := h z hz hzρ
    have := h1.sub h2
    rw [sub_self] at this
    convert this using 1
    funext n
    simp [sub_mul]
  funext n
  have := congrFun h0 n
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- A series over `ℤ` supported on `ℕ` is a series over `ℕ`. -/
theorem hasSum_nat_of_hasSum_int {f : ℤ → ℂ} {F : ℂ} (hf : ∀ n : ℤ, n < 0 → f n = 0)
    (h : HasSum f F) : HasSum (fun n : ℕ => f n) F := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
  refine (hinj.hasSum_iff fun x hx => hf x ?_).2 h
  by_contra hx'
  exact hx ⟨x.toNat, by simp only; omega⟩

end PowerSeries

section PolynomialFunction

/-- A function on `ℂˣ` given by a polynomial. -/
def IsPolynomialFn (F : ℂˣ → ℂ) : Prop :=
  ∃ Q : Polynomial ℂ, ∀ X : ℂˣ, F X = Q.eval (X : ℂ)

theorem isPolynomialFn_const (z : ℂ) : IsPolynomialFn fun _ => z :=
  ⟨Polynomial.C z, fun _ => by simp⟩

theorem isPolynomialFn_id : IsPolynomialFn fun X => (X : ℂ) :=
  ⟨Polynomial.X, fun _ => by simp⟩

theorem IsPolynomialFn.add {F G : ℂˣ → ℂ} (hF : IsPolynomialFn F) (hG : IsPolynomialFn G) :
    IsPolynomialFn fun X => F X + G X := by
  obtain ⟨P, hP⟩ := hF
  obtain ⟨Q, hQ⟩ := hG
  exact ⟨P + Q, fun X => by show F X + G X = _; rw [hP, hQ, Polynomial.eval_add]⟩

theorem IsPolynomialFn.mul {F G : ℂˣ → ℂ} (hF : IsPolynomialFn F) (hG : IsPolynomialFn G) :
    IsPolynomialFn fun X => F X * G X := by
  obtain ⟨P, hP⟩ := hF
  obtain ⟨Q, hQ⟩ := hG
  exact ⟨P * Q, fun X => by show F X * G X = _; rw [hP, hQ, Polynomial.eval_mul]⟩

theorem IsPolynomialFn.pow {F : ℂˣ → ℂ} (hF : IsPolynomialFn F) (n : ℕ) :
    IsPolynomialFn fun X => F X ^ n := by
  obtain ⟨P, hP⟩ := hF
  exact ⟨P ^ n, fun X => by show F X ^ n = _; rw [hP, Polynomial.eval_pow]⟩

theorem IsPolynomialFn.neg {F : ℂˣ → ℂ} (hF : IsPolynomialFn F) :
    IsPolynomialFn fun X => -F X := by
  obtain ⟨P, hP⟩ := hF
  exact ⟨-P, fun X => by show -F X = _; rw [hP, Polynomial.eval_neg]⟩

theorem IsPolynomialFn.congr {F G : ℂˣ → ℂ} (hF : IsPolynomialFn F) (h : ∀ X, F X = G X) :
    IsPolynomialFn G := by
  obtain ⟨P, hP⟩ := hF
  exact ⟨P, fun X => by rw [← h, hP]⟩

theorem isPolynomialFn_sum {ι : Type*} (s : Finset ι) {F : ι → ℂˣ → ℂ}
    (hF : ∀ i ∈ s, IsPolynomialFn (F i)) : IsPolynomialFn fun X => ∑ i ∈ s, F i X := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isPolynomialFn_const 0).congr fun X => by simp
  | insert i s hi ih =>
    refine ((hF i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))).congr fun X => ?_
    rw [Finset.sum_insert hi]

theorem isPolynomialFn_prod {ι : Type*} (s : Finset ι) {F : ι → ℂˣ → ℂ}
    (hF : ∀ i ∈ s, IsPolynomialFn (F i)) : IsPolynomialFn fun X => ∏ i ∈ s, F i X := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isPolynomialFn_const 1).congr fun X => by simp
  | insert i s hi ih =>
    refine ((hF i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))).congr fun X => ?_
    rw [Finset.prod_insert hi]

/-- Evaluations of a multivariate polynomial at polynomial coordinates are polynomial. -/
theorem isPolynomialFn_mvEval {σ : Type*} (P : MvPolynomial σ ℂ) {x : σ → ℂˣ → ℂ}
    (hx : ∀ i, IsPolynomialFn (x i)) :
    IsPolynomialFn fun X => MvPolynomial.eval (fun i => x i X) P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact (isPolynomialFn_const a).congr fun X => by simp
  | add P Q hP hQ => exact (hP.add hQ).congr fun X => by simp
  | mul_X P i hP => exact (hP.mul (hx i)).congr fun X => by simp

/-- **Polynomial functions agreeing on an infinite set agree everywhere.** -/
theorem IsPolynomialFn.eq_of_infinite {F G : ℂˣ → ℂ} (hF : IsPolynomialFn F)
    (hG : IsPolynomialFn G) {S : Set ℂˣ} (hS : S.Infinite) (h : ∀ X ∈ S, F X = G X) (X : ℂˣ) :
    F X = G X := by
  obtain ⟨P, hP⟩ := hF
  obtain ⟨Q, hQ⟩ := hG
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := (fun X : ℂˣ => (X : ℂ)) '' S)
    · rintro _ ⟨Y, hY, rfl⟩
      change Polynomial.eval (Y : ℂ) P = Polynomial.eval (Y : ℂ) Q
      rw [← hP, ← hQ, h Y hY]
    · exact hS.image Units.val_injective.injOn
  rw [hP, hQ, hPQ]

/-- For `ρ > 0`, the nonzero complex numbers of norm `< ρ` form an infinite set. -/
theorem infinite_small_units {ρ : ℝ} (hρ : 0 < ρ) :
    ({X : ℂˣ | ‖(X : ℂ)‖ < ρ}).Infinite := by
  set g : ℕ → ℂˣ := fun n => Units.mk0 ((ρ / (n + 2) : ℝ) : ℂ) (by
    have : (0 : ℝ) < ρ / (n + 2) := by positivity
    exact_mod_cast this.ne')
  have hg : Function.Injective g := by
    intro m n hmn
    have h1 := congrArg (fun X : ℂˣ => (X : ℂ)) hmn
    simp only [g, Units.val_mk0, Complex.ofReal_inj] at h1
    have hm : (0 : ℝ) < m + 2 := by positivity
    have hn : (0 : ℝ) < n + 2 := by positivity
    rw [div_eq_div_iff hm.ne' hn.ne'] at h1
    have h2 := mul_left_cancel₀ hρ.ne' h1
    have : (m : ℝ) = n := by linarith
    exact_mod_cast this
  refine Set.infinite_of_injective_forall_mem hg fun n => ?_
  simp only [Set.mem_ofPred_eq, g, Units.val_mk0, Complex.norm_real]
  have hpos : (0 : ℝ) < ρ / (n + 2) := by positivity
  rw [Real.norm_of_nonneg hpos.le, div_lt_iff₀ (by positivity)]
  nlinarith

/-- A function on `ℂˣ` given by a Laurent polynomial. -/
def IsLaurentFn (F : ℂˣ → ℂ) : Prop :=
  ∃ (N : ℕ) (Q : Polynomial ℂ), ∀ X : ℂˣ, (X : ℂ) ^ N * F X = Q.eval (X : ℂ)

theorem IsPolynomialFn.isLaurentFn {F : ℂˣ → ℂ} (hF : IsPolynomialFn F) : IsLaurentFn F := by
  obtain ⟨Q, hQ⟩ := hF
  exact ⟨0, Q, fun X => by rw [pow_zero, one_mul, hQ]⟩

theorem IsLaurentFn.congr {F G : ℂˣ → ℂ} (hF : IsLaurentFn F) (h : ∀ X, F X = G X) :
    IsLaurentFn G := by
  obtain ⟨N, Q, hQ⟩ := hF
  exact ⟨N, Q, fun X => by rw [← h, hQ]⟩

theorem IsLaurentFn.add {F G : ℂˣ → ℂ} (hF : IsLaurentFn F) (hG : IsLaurentFn G) :
    IsLaurentFn fun X => F X + G X := by
  obtain ⟨N, P, hP⟩ := hF
  obtain ⟨M, Q, hQ⟩ := hG
  refine ⟨N + M, Polynomial.X ^ M * P + Polynomial.X ^ N * Q, fun X => ?_⟩
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_pow, Polynomial.eval_X, ← hP, ← hQ]
  ring

theorem IsLaurentFn.mul {F G : ℂˣ → ℂ} (hF : IsLaurentFn F) (hG : IsLaurentFn G) :
    IsLaurentFn fun X => F X * G X := by
  obtain ⟨N, P, hP⟩ := hF
  obtain ⟨M, Q, hQ⟩ := hG
  refine ⟨N + M, P * Q, fun X => ?_⟩
  rw [Polynomial.eval_mul, ← hP, ← hQ]
  ring

theorem isLaurentFn_const (z : ℂ) : IsLaurentFn fun _ => z := (isPolynomialFn_const z).isLaurentFn

theorem isLaurentFn_zpow (n : ℤ) : IsLaurentFn fun X => (X : ℂ) ^ n := by
  rcases le_or_gt 0 n with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact ((isPolynomialFn_id.pow m).isLaurentFn).congr fun X => by simp
  · refine ⟨n.natAbs, 1, fun X => ?_⟩
    have hX : (X : ℂ) ≠ 0 := X.ne_zero
    rw [Polynomial.eval_one, ← zpow_natCast, ← zpow_add₀ hX]
    have : ((n.natAbs : ℕ) : ℤ) + n = 0 := by omega
    rw [this, zpow_zero]

theorem isLaurentFn_sum {ι : Type*} (s : Finset ι) {F : ι → ℂˣ → ℂ}
    (hF : ∀ i ∈ s, IsLaurentFn (F i)) : IsLaurentFn fun X => ∑ i ∈ s, F i X := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isLaurentFn_const 0).congr fun X => by simp
  | insert i s hi ih =>
    refine ((hF i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))).congr fun X => ?_
    rw [Finset.sum_insert hi]

theorem isLaurentFn_prod {ι : Type*} (s : Finset ι) {F : ι → ℂˣ → ℂ}
    (hF : ∀ i ∈ s, IsLaurentFn (F i)) : IsLaurentFn fun X => ∏ i ∈ s, F i X := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isLaurentFn_const 1).congr fun X => by simp
  | insert i s hi ih =>
    refine ((hF i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))).congr fun X => ?_
    rw [Finset.prod_insert hi]

/-- **Laurent functions agreeing on an infinite set agree everywhere.** -/
theorem IsLaurentFn.eq_of_infinite {F G : ℂˣ → ℂ} (hF : IsLaurentFn F) (hG : IsLaurentFn G)
    {S : Set ℂˣ} (hS : S.Infinite) (h : ∀ X ∈ S, F X = G X) (X : ℂˣ) : F X = G X := by
  obtain ⟨N, P, hP⟩ := hF
  obtain ⟨M, Q, hQ⟩ := hG
  have hP' : IsPolynomialFn fun X : ℂˣ => (X : ℂ) ^ (N + M) * F X :=
    ⟨Polynomial.X ^ M * P, fun X => by
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, ← hP]; ring⟩
  have hQ' : IsPolynomialFn fun X : ℂˣ => (X : ℂ) ^ (N + M) * G X :=
    ⟨Polynomial.X ^ N * Q, fun X => by
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, ← hQ]; ring⟩
  have h2 := hP'.eq_of_infinite hQ' hS (fun Y hY => by rw [h Y hY]) X
  have hX : (X : ℂ) ^ (N + M) ≠ 0 := pow_ne_zero _ X.ne_zero
  exact mul_left_cancel₀ hX h2

end PolynomialFunction

end Langlands.Shahidi.OpenCell
