import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Maximal weighted coefficients of products of linear forms -/

noncomputable section

namespace Langlands.Analytic

open MvPolynomial

/-- The multiplicative weight of a monomial for prescribed variable weights. -/
def monomialWeight {σ : Type*} (w : σ → ℝ) (d : σ →₀ ℕ) : ℝ :=
  d.prod fun j k => w j ^ k

theorem monomialWeight_pos {σ : Type*} {w : σ → ℝ} (hw : ∀ j, 0 < w j)
    (d : σ →₀ ℕ) : 0 < monomialWeight w d :=
  Finset.prod_pos fun j _ => pow_pos (hw j) _

/-- Some maximal weighted coefficient uses variable `0` with positive exponent
if and only if the coefficient of variable `0` is maximal in some factor. -/
theorem exists_maximalWeightedCoeff_pos_iff {L ι : Type*} [NormedField L]
    [IsUltrametricDist L] [Fintype ι] {n : ℕ} (w : Fin (n + 1) → ℝ)
    (hw : ∀ j, 0 < w j) (b : ι → Fin (n + 1) → L)
    (hb : ∀ i, ∃ j, b i j ≠ 0) :
    let P : MvPolynomial (Fin (n + 1)) L := ∏ i, ∑ j, C (b i j) * X j
    (∃ d : Fin (n + 1) →₀ ℕ, 0 < d 0 ∧
      ∀ k, ‖P.coeff k‖ * monomialWeight w k ≤ ‖P.coeff d‖ * monomialWeight w d) ↔
      ∃ i, ∀ j, ‖b i j‖ * w j ≤ ‖b i 0‖ * w 0 := by
  classical
  intro P
  let score (i : ι) (j : Fin (n + 1)) := ‖b i j‖ * w j
  let choices (i : ι) := Finset.univ.filter fun j => ∀ k, score i k ≤ score i j
  have hchoices (i : ι) : (choices i).Nonempty := by
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (score i) Finset.univ_nonempty
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k => hj k (Finset.mem_univ _)⟩⟩
  let best (i : ι) := (choices i).min' (hchoices i)
  have hbest (i : ι) (j : Fin (n + 1)) : score i j ≤ score i (best i) :=
    (Finset.mem_filter.mp ((choices i).min'_mem (hchoices i))).2 j
  have hleast (i : ι) (j : Fin (n + 1)) (h : score i j = score i (best i)) :
      best i ≤ j :=
    (choices i).min'_le j <| Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun k => (hbest i k).trans_eq h.symm⟩
  have hnonneg (i : ι) (j : Fin (n + 1)) : 0 ≤ score i j :=
    mul_nonneg (norm_nonneg _) (hw j).le
  have hpos (i : ι) : 0 < score i (best i) := by
    obtain ⟨j, hj⟩ := hb i
    exact (mul_pos (norm_pos_iff.mpr hj) (hw j)).trans_le (hbest i j)
  let deg (a : ι → Fin (n + 1)) : Fin (n + 1) →₀ ℕ := ∑ i, Finsupp.single (a i) 1
  let term (a : ι → Fin (n + 1)) : L := ∏ i, b i (a i)
  let value (a : ι → Fin (n + 1)) : ℝ := ∏ i, score i (a i)
  have hvalue_pos : 0 < value best := Finset.prod_pos fun i _ => hpos i
  have hvalue_le (a : ι → Fin (n + 1)) : value a ≤ value best :=
    Finset.prod_le_prod₀ (fun i _ => hnonneg i _) (fun i _ => hbest i _)
  have hfactor (a : ι → Fin (n + 1)) (ha : value a = value best) (i : ι) :
      score i (a i) = score i (best i) := by
    have hpositive (j : ι) : 0 < score j (a j) := by
      refine lt_of_le_of_ne (hnonneg j _) fun h => ?_
      have hzero : value a = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h.symm
      exact hvalue_pos.ne' (ha.symm.trans hzero)
    refine le_antisymm (hbest i _) (le_of_not_gt fun h => ?_)
    exact (Finset.prod_lt_prod₀ (fun j _ => hpositive j) (fun j _ => hbest j _)
      ⟨i, Finset.mem_univ i, h⟩).ne ha
  have hindexSum (a : ι → Fin (n + 1)) :
      (deg a).sum (fun j k => j.val * k) = ∑ i, (a i).val := by
    dsimp only [deg]
    rw [← Finsupp.sum_finsetSum_index (fun j : Fin (n + 1) => mul_zero j.val)
      (fun j : Fin (n + 1) => Nat.mul_add j.val)]
    simp
  have hunique (a : ι → Fin (n + 1)) (hd : deg a = deg best)
      (h : value a = value best) : a = best := by
    funext i
    have hle (j : ι) : (best j).val ≤ (a j).val := hleast j _ (hfactor a h j)
    refine Fin.ext (le_antisymm (le_of_not_gt fun hi => ?_) (hle i))
    have hlt := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩
    exact hlt.ne (by rw [← hindexSum best, ← hindexSum a, hd])
  have hdeg_zero (a : ι → Fin (n + 1)) : 0 < deg a 0 ↔ ∃ i, a i = 0 := by
    simp only [deg, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    simp [apply_ite]
  have hterm (a : ι → Fin (n + 1)) : ‖term a‖ * monomialWeight w (deg a) = value a := by
    dsimp only [term, monomialWeight, deg, value, score]
    rw [← Finsupp.prod_finsetSum_index (fun j => pow_zero (w j))
      (fun j k l => pow_add (w j) k l), norm_prod, Finset.prod_mul_distrib]
    simp
  have hexpand : P = ∑ a : ι → Fin (n + 1), monomial (deg a) (term a) := by
    dsimp only [P, deg, term]
    rw [Fintype.prod_sum]
    simp_rw [C_mul_X_eq_monomial, monomial_sum_prod]
  let tuples (d : Fin (n + 1) →₀ ℕ) := Finset.univ.filter fun a => deg a = d
  have hcoeff (d : Fin (n + 1) →₀ ℕ) : P.coeff d = ∑ a ∈ tuples d, term a := by
    rw [hexpand, coeff_sum]
    simp only [tuples, Finset.sum_filter, coeff_monomial]
  have hna : IsNonarchimedean (norm : L → ℝ) := IsUltrametricDist.isNonarchimedean_norm
  have hbest_coeff : ‖P.coeff (deg best)‖ * monomialWeight w (deg best) = value best := by
    rw [hcoeff, ← hterm best]
    congr 1
    apply hna.apply_sum_eq_of_lt term norm_neg (k := best)
    · simp [tuples]
    · intro a ha hane
      have hd := (Finset.mem_filter.mp ha).2
      have hlt := lt_of_le_of_ne (hvalue_le a) (fun heq => hane (hunique a hd heq))
      rw [← hterm a, ← hterm best, hd] at hlt
      exact lt_of_mul_lt_mul_right hlt (monomialWeight_pos hw _).le
  have hbound (d : Fin (n + 1) →₀ ℕ) (hd : (tuples d).Nonempty) :
      ∃ a, deg a = d ∧ ‖P.coeff d‖ * monomialWeight w d ≤ value a := by
    obtain ⟨a, ha, hn⟩ := hna.finset_image_add_of_nonempty term hd
    have hda := (Finset.mem_filter.mp ha).2
    refine ⟨a, hda, ?_⟩
    rw [hcoeff, ← hterm a, hda]
    exact mul_le_mul_of_nonneg_right hn (monomialWeight_pos hw _).le
  constructor
  · rintro ⟨d, hd, hmax⟩
    have hpos_d := hvalue_pos.trans_le (hbest_coeff ▸ hmax (deg best))
    have ht : (tuples d).Nonempty := by
      by_contra h
      rw [hcoeff, Finset.not_nonempty_iff_eq_empty.mp h] at hpos_d
      simp at hpos_d
    obtain ⟨a, hda, hbound_a⟩ := hbound d ht
    have heq : value a = value best :=
      le_antisymm (hvalue_le a) (hbest_coeff ▸ (hmax (deg best)).trans hbound_a)
    obtain ⟨i, hi⟩ := (hdeg_zero a).mp (hda ▸ hd)
    refine ⟨i, fun j => ?_⟩
    exact (hbest i j).trans_eq ((hfactor a heq i).symm.trans (congrArg (score i) hi))
  · rintro ⟨i, hi⟩
    have hzero : best i = 0 := le_antisymm
      (hleast i 0 (le_antisymm (hbest i 0) (hi (best i)))) (Fin.zero_le _)
    refine ⟨deg best, (hdeg_zero best).2 ⟨i, hzero⟩, fun d => ?_⟩
    rw [hbest_coeff]
    by_cases ht : (tuples d).Nonempty
    · obtain ⟨a, _, ha⟩ := hbound d ht
      exact ha.trans (hvalue_le a)
    · rw [hcoeff, Finset.not_nonempty_iff_eq_empty.mp ht]
      simpa using hvalue_pos.le

end Langlands.Analytic
