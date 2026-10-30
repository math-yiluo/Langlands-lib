import Langlands.Analysis.EventuallyRecurrentLaurentSeriesStatement
import Langlands.Analysis.LinearRecurrenceGeneratingSeriesProof
import Langlands.Representation.RankinSelberg.LaurentEvaluation

/-!
# Proof of uniform Laurent rationality for eventually recurrent sequences

The radius and the reverse characteristic polynomial `Q` come from the natural
generating-series theorem. For a sequence `c` vanishing below `L` whose tail
`a j = c (j + N)` is recurrent, the bilateral series at `w = z ^ m` splits into
the finite head over `L ≤ n < N` and `w ^ N` times the natural series of `a`.
The head is the Laurent polynomial `H = ∑ c n * T (m * n)`, and the tail is
`B / Q(X ^ m)` with `B = X ^ (m * N) * A(X ^ m)`, so `R = H + B / Q(X ^ m)` is
cleared by `D = Q(X ^ m)` with numerator `H * D + B`.
-/

namespace Langlands.Analysis

open Finset Polynomial
open Langlands.RankinSelberg

namespace EventuallyRecurrentLaurentSeries

/-- A bilateral sequence vanishing below `L`, whose tail from `N ≥ L` is
summable, is summable; its sum is the finite head plus the tail sum. -/
theorem summable_and_tsum_split (f : ℤ → ℂ) (L : ℤ) (N : ℕ)
    (hf : ∀ n : ℤ, n < L → f n = 0)
    (htail : Summable (fun j : ℕ => f ((j : ℤ) + (N : ℤ)))) :
    Summable f ∧
      ∑' n : ℤ, f n = ∑ n ∈ Ico L (N : ℤ), f n + ∑' j : ℕ, f ((j : ℤ) + (N : ℤ)) := by
  classical
  set g : ℤ → ℂ := fun n => if n < (N : ℤ) then f n else 0 with hg
  set h : ℤ → ℂ := fun n => if (N : ℤ) ≤ n then f n else 0 with hh
  have hfgh : f = g + h := by
    funext n
    simp only [hg, hh, Pi.add_apply]
    split_ifs with h1 h2 h2 <;> first | omega | simp
  have hgfin : ∀ n ∉ Ico L (N : ℤ), g n = 0 := by
    intro n hn
    rw [mem_Ico, not_and_or, not_le, not_lt] at hn
    simp only [hg]
    split_ifs with h1
    · rcases hn with hn | hn
      · exact hf n hn
      · omega
    · rfl
  have hgs : Summable g := summable_of_ne_finset_zero hgfin
  have hgt : ∑' n : ℤ, g n = ∑ n ∈ Ico L (N : ℤ), f n := by
    rw [tsum_eq_sum hgfin]
    refine sum_congr rfl fun n hn => ?_
    rw [mem_Ico] at hn
    simp [hg, hn.2]
  set e : ℕ → ℤ := fun j => (j : ℤ) + (N : ℤ) with he
  have heinj : Function.Injective e := fun i j hij => by
    simp only [he] at hij
    omega
  have hcomp : h ∘ e = fun j : ℕ => f ((j : ℤ) + (N : ℤ)) := by
    funext j
    simp [hh, he]
  have hrange : ∀ n ∉ Set.range e, h n = 0 := by
    intro n hn
    simp only [hh]
    split_ifs with h1
    · exact absurd ⟨(n - N).toNat, by simp only [he]; omega⟩ hn
    · rfl
  have hhs : Summable h := by
    rw [← heinj.summable_iff hrange, hcomp]
    exact htail
  have hht : ∑' n : ℤ, h n = ∑' j : ℕ, f ((j : ℤ) + (N : ℤ)) := by
    rw [← heinj.tsum_eq (Function.support_subset_iff'.2 hrange)]
    exact congrArg tsum hcomp
  have hfs : Summable f := by
    rw [hfgh]
    exact hgs.add hhs
  have hft : ∑' n : ℤ, f n = ∑' n : ℤ, g n + ∑' n : ℤ, h n := by
    rw [← Summable.tsum_add hgs hhs]
    exact congrArg tsum hfgh
  exact ⟨hfs, by rw [hft, hgt, hht]⟩

end EventuallyRecurrentLaurentSeries

open EventuallyRecurrentLaurentSeries in
/-- Proof of `EventuallyRecurrentLaurentSeriesStatement`, with the radius of
`linearRecurrenceGeneratingSeriesStatement_proof`. -/
theorem eventuallyRecurrentLaurentSeriesStatement_proof :
    EventuallyRecurrentLaurentSeriesStatement := by
  intro E Q
  obtain ⟨hQ0, ρ, hρ, hsol⟩ := linearRecurrenceGeneratingSeriesStatement_proof E
  refine ⟨hQ0, ρ, hρ, fun m hm => ?_⟩
  set Qm : ℂ[X] := Q.comp (X ^ m) with hQmdef
  have hQm0 : Qm.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, hQmdef, eval_comp, eval_pow, eval_X, zero_pow hm.ne',
      ← coeff_zero_eq_eval_zero]
    exact hQ0
  have hQm : Qm ≠ 0 := fun h => by simp [h] at hQm0
  refine ⟨fun h => hQm (Polynomial.toLaurent_eq_zero.1 h), ?_⟩
  intro c L N hLN hc hrec
  obtain ⟨A, hA⟩ := hsol _ hrec
  set H : LaurentPolynomial ℂ :=
    ∑ n ∈ Ico L (N : ℤ), LaurentPolynomial.C (c n) * LaurentPolynomial.T ((m : ℤ) * n) with hH
  set B : ℂ[X] := X ^ (m * N) * A.comp (X ^ m) with hB
  refine ⟨laurentToRatFunc H + algebraMap ℂ[X] (RatFunc ℂ) B / algebraMap ℂ[X] (RatFunc ℂ) Qm,
    H * Qm.toLaurent + B.toLaurent, ?_, ?_⟩
  · have hQm' : algebraMap ℂ[X] (RatFunc ℂ) Qm ≠ 0 := RatFunc.algebraMap_ne_zero hQm
    rw [map_add, map_mul, laurentToRatFunc_toLaurent, laurentToRatFunc_toLaurent, mul_add,
      mul_div_assoc', mul_div_cancel_left₀ _ hQm']
    ring
  · intro z hz hzρ
    set w : ℂ := z ^ m with hw
    have hw0 : w ≠ 0 := pow_ne_zero _ hz
    obtain ⟨hsum, hQw, htsum⟩ := hA w hzρ
    have htail : ∀ j : ℕ, c ((j : ℤ) + (N : ℤ)) * w ^ ((j : ℤ) + (N : ℤ)) =
        w ^ N * (c ((j : ℤ) + (N : ℤ)) * w ^ j) := by
      intro j
      rw [zpow_add₀ hw0, zpow_natCast, zpow_natCast]
      ring
    obtain ⟨hS, hT⟩ := summable_and_tsum_split (fun n : ℤ => c n * w ^ n) L N
      (fun n hn => by simp [hc n hn])
      (by simp_rw [htail]; exact hsum.mul_left _)
    refine ⟨hS, ?_⟩
    set x : ℂˣ := Units.mk0 z hz with hx
    have hxz : (x : ℂ) = z := by rw [hx, Units.val_mk0]
    obtain ⟨hHreg, hHeval⟩ := laurentToRatFunc_regular_and_eval x H
    rw [hxz] at hHreg hHeval
    have hQmz : Qm.eval z = Q.eval w := by
      rw [hQmdef, eval_comp, eval_pow, eval_X]
    obtain ⟨hBreg, hBeval⟩ := regular_and_eval_div z B Qm (hQmz ▸ hQw)
    refine ⟨fun h0 => ?_, ?_⟩
    · have hdvd := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd _ _) h0
      rw [eval_mul, mul_eq_zero] at hdvd
      exact hdvd.elim hHreg hBreg
    · rw [RatFunc.eval_add (RingHom.id ℂ) z hHreg hBreg, hHeval, hBeval, hT, hQmz]
      simp_rw [htail]
      rw [tsum_mul_left, htsum, hH, map_sum]
      have hBz : B.eval z = w ^ N * A.eval w := by
        rw [hB, eval_mul, eval_pow, eval_X, eval_comp, eval_pow, eval_X, pow_mul]
      rw [hBz, mul_div_assoc]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [map_mul, laurentEval_C, laurentEval_T, hxz, zpow_mul, zpow_natCast]

end Langlands.Analysis
