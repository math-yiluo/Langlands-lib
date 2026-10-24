import Langlands.Representation.RankinSelberg.RationalContinuationLinearStatement
import Langlands.Representation.RankinSelberg.LocalFactor

/-! Finite linear continuation and fixed-denominator closure.
The finite continuation helpers are adapted from Worker 329's shared draft.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial
open scoped BigOperators

namespace RationalContinuationLinear

/-- Addition does not introduce a pole away from both original denominators. -/
private theorem denom_eval_add_ne_zero {R S : RationalFunctions} {x : ℂ}
    (hR : R.denom.eval x ≠ 0) (hS : S.denom.eval x ≠ 0) :
    (R + S).denom.eval x ≠ 0 := by
  intro h0
  have h := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) x
    (RatFunc.denom_add_dvd R S) h0
  simp only [eval₂_id, eval_mul, mul_eq_zero, hR, hS, or_self] at h

/-- Continuations add on the intersection of their right half-planes. -/
theorem continuation_add {q : ℕ} {f g : ℂ → ℂ} {R S : RationalFunctions}
    (hR : HasRationalContinuation q f R) (hS : HasRationalContinuation q g S) :
    HasRationalContinuation q (fun s => f s + g s) (R + S) := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := hS
  refine ⟨max a b, fun s hs => ?_⟩
  obtain ⟨hdR, heR⟩ := ha s ((le_max_left a b).trans_lt hs)
  obtain ⟨hdS, heS⟩ := hb s ((le_max_right a b).trans_lt hs)
  exact ⟨denom_eval_add_ne_zero hdR hdS,
    (congrArg₂ (· + ·) heR heS).trans (RatFunc.eval_add _ _ hdR hdS).symm⟩

/-- A finite sum of continuations has the sum of their rational functions. -/
theorem continuation_sum {ι : Type*} {q : ℕ} (t : Finset ι)
    (f : ι → ℂ → ℂ) (R : ι → RationalFunctions)
    (h : ∀ i ∈ t, HasRationalContinuation q (f i) (R i)) :
    HasRationalContinuation q (fun s => ∑ i ∈ t, f i s) (∑ i ∈ t, R i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp [RatFunc.denom_zero]⟩
  | @insert i t hi ih =>
    have hsum := continuation_add (h i (Finset.mem_insert_self i t))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hsum

/-- Constant linear combinations preserve continuation, including zero coefficients. -/
theorem continuation_linear_combination {ι : Type*} {q : ℕ} (t : Finset ι)
    (c : ι → ℂ) (f : ι → ℂ → ℂ) (R : ι → RationalFunctions)
    (h : ∀ i ∈ t, HasRationalContinuation q (f i) (R i)) :
    HasRationalContinuation q (fun s => ∑ i ∈ t, c i * f i s)
      (∑ i ∈ t, RatFunc.C (c i) * R i) :=
  continuation_sum t _ _ (fun i hi => hasRationalContinuation_const_mul (c i) (h i hi))

/-- Transfer continuation across equality on a right half-plane. -/
theorem continuation_of_eq_on_right {q : ℕ} {f g : ℂ → ℂ} {R : RationalFunctions}
    (hR : HasRationalContinuation q f R)
    (hfg : ∃ b : ℝ, ∀ s : ℂ, b < s.re → g s = f s) :
    HasRationalContinuation q g R := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := hfg
  refine ⟨max a b, fun s hs => ?_⟩
  obtain ⟨hd, he⟩ := ha s ((le_max_left a b).trans_lt hs)
  exact ⟨hd, (hb s ((le_max_right a b).trans_lt hs)).trans he⟩

/-- Coefficient integrals act by constants already in the Laurent coefficient ring. -/
theorem linear_combination_mem_span {ι : Type*} {values : Set RationalFunctions}
    (t : Finset ι) (c : ι → ℂ) (R : ι → RationalFunctions)
    (hR : ∀ i ∈ t, R i ∈ values) :
    (∑ i ∈ t, RatFunc.C (c i) * R i) ∈ zetaSpan values := by
  apply Submodule.sum_mem
  intro i hi
  have h := Submodule.smul_mem (zetaSpan values) (LaurentPolynomial.C (c i))
    (mem_zetaSpan (hR i hi))
  simpa only [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C] using h

/-- A specified Laurent denominator clearing generators clears their entire span. -/
theorem denominator_clears_span {values : Set RationalFunctions}
    (d : LaurentCoefficients)
    (h : ∀ R ∈ values, ∃ P : LaurentCoefficients,
      laurentToRatFunc P = laurentToRatFunc d * R)
    {R : RationalFunctions} (hR : R ∈ zetaSpan values) :
    ∃ P : LaurentCoefficients, laurentToRatFunc P = laurentToRatFunc d * R := by
  induction hR using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨P, hP⟩ := ihx
    obtain ⟨Q, hQ⟩ := ihy
    exact ⟨P + Q, by rw [map_add, hP, hQ, mul_add]⟩
  | smul a x hx ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨a * P, ?_⟩
    rw [map_mul, hP, Algebra.smul_def, algebraMap_laurent, mul_left_comm]

/-- A common denominator transfers to any set contained in the original span. -/
theorem commonDenominator_of_mem_span {values other : Set RationalFunctions}
    (h : HasCommonDenominator values) (ho : ∀ R ∈ other, R ∈ zetaSpan values) :
    HasCommonDenominator other := by
  obtain ⟨d, hd, hclear⟩ := h
  exact ⟨d, hd, fun R hR => denominator_clears_span d hclear (ho R hR)⟩

end RationalContinuationLinear

/-- Finite linear continuation and closure under the same clearing denominator. -/
theorem rationalContinuationLinear : RationalContinuationLinearStatement := by
  constructor
  · intro q r f R c h
    exact RationalContinuationLinear.continuation_linear_combination
      Finset.univ c f R (fun i _ => h i)
  · intro values d h R hR
    exact RationalContinuationLinear.denominator_clears_span d h hR

end Langlands.RankinSelberg
