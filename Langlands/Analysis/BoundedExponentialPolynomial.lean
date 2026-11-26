import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Bounded exponential polynomials with exponents of negative real part

A function `t ↦ ∑ᵢ e^{t zᵢ} pᵢ(t)` on `ℝ`, with complex polynomials `pᵢ` and exponents of
negative real part, that is bounded on `ℝ` vanishes identically (Bernstein–Lapid, proof of the
lemma of §6.4, by difference operators). -/

noncomputable section

open Polynomial Filter Topology

set_option autoImplicit false

namespace Langlands.Analysis

/-- The exponential polynomial `t ↦ ∑_{i ∈ S} e^{t zᵢ} pᵢ(t)`. -/
def expPolynomial {ι : Type*} (S : Finset ι) (z : ι → ℂ) (p : ι → ℂ[X]) (t : ℝ) : ℂ :=
  ∑ i ∈ S, Complex.exp (t * z i) * (p i).eval (t : ℂ)

/-- The complexity of a polynomial: `0` for the zero polynomial, otherwise degree plus one. -/
private def weight (p : ℂ[X]) : ℕ := if p = 0 then 0 else p.natDegree + 1

private theorem weight_le (a b : ℂ) (p : ℂ[X]) :
    weight (C a * taylor 1 p - C b * p) ≤ weight p := by
  unfold weight
  by_cases hp : p = 0
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    split_ifs with hq
    · omega
    · have h1 : (C a * taylor 1 p).natDegree ≤ p.natDegree :=
        (natDegree_C_mul_le a _).trans (natDegree_taylor p 1).le
      have h2 : (C b * p).natDegree ≤ p.natDegree := natDegree_C_mul_le b p
      have := (natDegree_sub_le _ _).trans (max_le h1 h2)
      omega

private theorem weight_lt (a : ℂ) (p : ℂ[X]) (hp : p ≠ 0) :
    weight (C a * taylor 1 p - C a * p) < weight p := by
  unfold weight
  simp only [hp, ↓reduceIte, ← mul_sub]
  split_ifs with hq
  · omega
  · have hd : taylor 1 p - p ≠ 0 := fun h => hq (by rw [h, mul_zero])
    have hlt : (taylor 1 p - p).natDegree < p.natDegree := by
      by_cases h0 : p.natDegree = 0
      · exfalso
        apply hd
        rw [eq_C_of_natDegree_eq_zero h0, taylor_C, sub_self]
      · have hdeg := degree_sub_lt_left (degree_taylor p 1) ((taylor_eq_zero 1 p).not.mpr hp)
          (leadingCoeff_taylor 1 p)
        exact (natDegree_lt_natDegree hd hdeg).trans_eq (natDegree_taylor p 1)
    have := natDegree_C_mul_le a (taylor 1 p - p)
    omega

private theorem weight_eq_zero {p : ℂ[X]} (h : weight p = 0) : p = 0 := by
  by_contra hp
  simp [weight, hp] at h

/-- A bounded exponential polynomial whose exponents all have negative real part vanishes. -/
theorem expPolynomial_eq_zero_of_bounded {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, (z i).re < 0) (p : ι → ℂ[X])
    (hb : ∃ C : ℝ, ∀ t : ℝ, ‖expPolynomial S z p t‖ ≤ C) (t : ℝ) :
    expPolynomial S z p t = 0 := by
  classical
  suffices h : ∀ m : ℕ, ∀ p : ι → ℂ[X], ∑ i ∈ S, weight (p i) = m →
      (∃ C : ℝ, ∀ t : ℝ, ‖expPolynomial S z p t‖ ≤ C) → ∀ t, expPolynomial S z p t = 0 from
    h _ p rfl hb t
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p hm hb t
  by_cases hall : ∀ i ∈ S, p i = 0
  · unfold expPolynomial
    exact Finset.sum_eq_zero fun i hi => by rw [hall i hi, eval_zero, mul_zero]
  push Not at hall
  obtain ⟨j, hj, hpj⟩ := hall
  obtain ⟨C₀, hC₀⟩ := hb
  let p' : ι → ℂ[X] := fun i =>
    Polynomial.C (Complex.exp (z i)) * taylor 1 (p i) - Polynomial.C (Complex.exp (z j)) * p i
  have hshift : ∀ s : ℝ, expPolynomial S z p' s =
      expPolynomial S z p (s + 1) - Complex.exp (z j) * expPolynomial S z p s := by
    intro s
    unfold expPolynomial
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [p', eval_sub, eval_mul, eval_C, taylor_eval]
    push_cast
    rw [add_mul, one_mul, Complex.exp_add]
    ring
  have hlt : ∑ i ∈ S, weight (p' i) < m := by
    rw [← hm]
    apply Finset.sum_lt_sum (fun i _ => weight_le _ _ _)
    exact ⟨j, hj, weight_lt _ _ hpj⟩
  have hzero := ih _ hlt p' rfl ⟨C₀ + ‖Complex.exp (z j)‖ * C₀, fun s => by
    rw [hshift]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    exact add_le_add (hC₀ _) (mul_le_mul_of_nonneg_left (hC₀ _) (norm_nonneg _))⟩
  have hrec : ∀ s : ℝ, expPolynomial S z p (s + 1) = Complex.exp (z j) * expPolynomial S z p s :=
    fun s => sub_eq_zero.mp ((hshift s).symm.trans (hzero s))
  have hpow : ∀ n : ℕ, expPolynomial S z p t =
      Complex.exp (z j) ^ n * expPolynomial S z p (t - n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ihn =>
      rw [ihn, pow_succ, mul_assoc, ← hrec]
      congr 2
      push_cast
      ring
  have hr : 0 < Real.exp (z j).re := Real.exp_pos _
  have hr1 : Real.exp (z j).re < 1 := Real.exp_lt_one_iff.mpr (hz j hj)
  have hbound : ∀ n : ℕ, ‖expPolynomial S z p t‖ ≤ Real.exp (z j).re ^ n * C₀ := by
    intro n
    rw [hpow n, norm_mul, norm_pow, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (hC₀ _) (pow_nonneg hr.le _)
  have hlim : Tendsto (fun n : ℕ => Real.exp (z j).re ^ n * C₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).mul_const C₀
  have hle : ‖expPolynomial S z p t‖ ≤ 0 := ge_of_tendsto' hlim hbound
  exact norm_le_zero_iff.mp hle

/-- On a line `t ↦ t • H` of a real vector space, a complex polynomial function of bounded
degree (`polynomialFunctions`) is a complex polynomial in `t`. -/
theorem exists_polynomial_eval_smul {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    {f : V → ℂ} (hf : f ∈ Langlands.Global.polynomialFunctions V n) (H : V) :
    ∃ q : ℂ[X], ∀ t : ℝ, f (t • H) = q.eval (t : ℂ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, -, ℓ, rfl⟩ := hf
    refine ⟨Polynomial.C (∏ j, ((ℓ j H : ℝ) : ℂ)) * X ^ k, fun t => ?_⟩
    simp only [map_smul, smul_eq_mul, Complex.ofReal_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, eval_mul, eval_C, eval_pow, eval_X]
    ring
  | zero => exact ⟨0, fun t => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨q₁, h₁⟩ := hf
    obtain ⟨q₂, h₂⟩ := hg
    exact ⟨q₁ + q₂, fun t => by simp [h₁, h₂]⟩
  | smul c f _ hf =>
    obtain ⟨q, hq⟩ := hf
    exact ⟨Polynomial.C c * q, fun t => by simp [hq]⟩

end Langlands.Analysis
