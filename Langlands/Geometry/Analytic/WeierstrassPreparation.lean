import Langlands.Geometry.Analytic.DistinguishedSeries
import Mathlib.Analysis.Normed.Ring.Units

/-! # Preparation of normalized distinguished restricted series -/

noncomputable section

universe u

namespace Langlands.Analytic.RestrictedSeries

open Polynomial

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]

/-- Any division decomposition by a small perturbation satisfies the sharp
bounds; the conclusion does not assume that the constructed quotient was used. -/
theorem norm_le_perturbed_monic_mul_add
    (p : Polynomial A) (hp : p.Monic) (hunit : ∀ n, ‖p.coeff n‖ ≤ 1)
    (h : Algebra A) (hh : ‖h‖ < 1) (q : Algebra A) (r : Polynomial A)
    (hr : r.degree < p.degree) :
    ‖q‖ ≤ ‖(ofPolynomial A p + h) * q + ofPolynomial A r‖ ∧
    ‖ofPolynomial A r‖ ≤ ‖(ofPolynomial A p + h) * q + ofPolynomial A r‖ := by
  let g := (ofPolynomial A p + h) * q + ofPolynomial A r
  have heq : ofPolynomial A p * q + ofPolynomial A r = g - h * q := by
    dsimp [g]
    ring
  have hest := norm_le_monic_mul_add p hp hunit q r hr
  rw [heq] at hest
  have hdiff : ‖g - h * q‖ ≤ max ‖g‖ (‖h‖ * ‖q‖) :=
    (show ‖g - h * q‖ ≤ max ‖g‖ ‖h * q‖ from by
      simpa only [sub_eq_add_neg, norm_neg] using
        IsUltrametricDist.norm_add_le_max g (-(h * q))).trans
      (max_le_max le_rfl (norm_mul_le _ _))
  have hq : ‖q‖ ≤ ‖g‖ := by
    by_contra hn
    have hlt : ‖g‖ < ‖q‖ := lt_of_not_ge hn
    have hpos : 0 < ‖q‖ := lt_of_le_of_lt (norm_nonneg g) hlt
    have hc : ‖h‖ * ‖q‖ < ‖q‖ := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hh hpos
    exact (not_lt_of_ge (hest.1.trans hdiff)) (max_lt hlt hc)
  exact ⟨hq, hest.2.trans (hdiff.trans (max_le le_rfl
    ((mul_le_of_le_one_left (norm_nonneg q) hh.le).trans hq)))⟩

variable [Nontrivial A]

/-- Sharp bounds for every decomposition with remainder degree below the
distinguished degree. -/
theorem norm_le_normalizedDistinguished_mul_add
    (f : Algebra A) (d : ℕ) (hf : IsNormalizedDistinguished f d)
    (q : Algebra A) (r : Polynomial A) (hr : r.degree < d) :
    ‖q‖ ≤ ‖f * q + ofPolynomial A r‖ ∧
    ‖ofPolynomial A r‖ ≤ ‖f * q + ofPolynomial A r‖ := by
  let p := trunc A (d + 1) f
  have hp := normalizedDistinguished_trunc_monic f d hf
  have hd : p.degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero,
      normalizedDistinguished_trunc_natDegree f d hf]
  have h := norm_le_perturbed_monic_mul_add p hp
    (normalizedDistinguished_trunc_coeff_le f d hf)
    (f - ofPolynomial A p) (normalizedDistinguished_tail_norm_lt_one f d hf)
    q r (by simpa only [hd] using hr)
  have heq : ofPolynomial A p + (f - ofPolynomial A p) = f := by abel
  simpa only [heq] using h

omit [IsUltrametricDist A] in
/-- Monic polynomials of the same degree have a difference of lower degree.
The bottom degree handles the case of constant monic polynomials. -/
theorem degree_X_pow_sub_monic_lt (p : Polynomial A) (hp : p.Monic)
    (d : ℕ) (hd : p.natDegree = d) :
    ((X : Polynomial A) ^ d - p).degree < d := by
  have hpd : p.degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hd]
  have h := Polynomial.degree_sub_lt_left
    (p := (X : Polynomial A) ^ d) (q := p)
    (by simpa only [Polynomial.degree_X_pow] using hpd.symm)
    (Polynomial.monic_X_pow d).ne_zero
    (by rw [(Polynomial.monic_X_pow d).leadingCoeff, hp.leadingCoeff])
  simpa only [Polynomial.degree_X_pow] using h

variable [NormOneClass A]

omit [Nontrivial A] in
private theorem norm_ofPolynomial_X_pow_le (d : ℕ) :
    ‖ofPolynomial A ((X : Polynomial A) ^ d)‖ ≤ 1 := by
  rw [norm_ofPolynomial]
  apply (polynomial_supNorm_le_iff _ 1).mpr
  intro n
  rw [Polynomial.coeff_X_pow]
  split_ifs <;> simp

variable [CompleteSpace A]

/-- Preparation for a normalized distinguished series. The unit is obtained
from the convergent geometric series of the constructed quotient's defect
from one, rather than assumed as part of the input. -/
theorem existsUnique_normalizedDistinguished_preparation
    (f : Algebra A) (d : ℕ) (hf : IsNormalizedDistinguished f d) :
    ∃! ew : (Algebra A)ˣ × Polynomial A,
      f = (ew.1 : Algebra A) * ofPolynomial A ew.2 ∧
      ew.2.Monic ∧ ew.2.natDegree = d ∧ ∀ n, ‖ew.2.coeff n‖ ≤ 1 := by
  let x : Polynomial A := X ^ d
  obtain ⟨qr, hqr, huniq⟩ :=
    existsUnique_normalizedDistinguished_division f d hf (ofPolynomial A x)
  obtain ⟨heq, hr, hqnorm, hrnorm⟩ := hqr
  have hxnorm : ‖ofPolynomial A x‖ ≤ 1 := norm_ofPolynomial_X_pow_le d
  have hqone : ‖qr.1‖ ≤ 1 := hqnorm.trans hxnorm
  let p := trunc A (d + 1) f
  have hp : p.Monic := normalizedDistinguished_trunc_monic f d hf
  have hpd : p.natDegree = d := normalizedDistinguished_trunc_natDegree f d hf
  have hpdegree : p.degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hpd]
  have hsp : (x - p).degree < d := degree_X_pow_sub_monic_lt p hp d hpd
  have hrd : (qr.2 - (x - p)).degree < p.degree := by
    rw [hpdegree]
    exact (Polynomial.degree_sub_le _ _).trans_lt (max_lt hr hsp)
  have hid : ofPolynomial A p * (qr.1 - 1) +
      ofPolynomial A (qr.2 - (x - p)) = -( (f - ofPolynomial A p) * qr.1) := by
    rw [map_sub, map_sub]
    calc
      _ = (f * qr.1 + ofPolynomial A qr.2) - ofPolynomial A x -
          (f - ofPolynomial A p) * qr.1 := by ring
      _ = _ := by rw [← heq, sub_self, zero_sub]
  have hclose : ‖qr.1 - 1‖ < 1 := by
    have hest := (norm_le_monic_mul_add p hp
      (normalizedDistinguished_trunc_coeff_le f d hf)
      (qr.1 - 1) (qr.2 - (x - p)) hrd).1
    rw [hid, norm_neg] at hest
    exact lt_of_le_of_lt
      (hest.trans ((norm_mul_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hqone)))
      (normalizedDistinguished_tail_norm_lt_one f d hf)
  let u : (Algebra A)ˣ := Units.oneSub (1 - qr.1) (by
    simpa only [norm_sub_rev] using hclose)
  have hu : (u : Algebra A) = qr.1 := by
    simp [u]
  let w := x - qr.2
  have hw : w.Monic := Polynomial.monic_X_pow_sub hr
  have hwd : w.natDegree = d := by
    have hd := Polynomial.degree_sub_eq_left_of_degree_lt (p := x) (q := qr.2)
      (by simpa only [x, Polynomial.degree_X_pow] using hr)
    have hd' : w.degree = (d : WithBot ℕ) := by
      simpa only [x, Polynomial.degree_X_pow] using hd
    rw [Polynomial.degree_eq_natDegree hw.ne_zero] at hd'
    exact WithBot.coe_injective hd'
  have hwval : ofPolynomial A w = f * qr.1 := by
    dsimp [w]
    rw [map_sub, heq, add_sub_cancel_right]
  have hwcoeff : ∀ n, ‖w.coeff n‖ ≤ 1 := by
    have hwnorm : ‖ofPolynomial A w‖ ≤ 1 := by
      dsimp [w]
      rw [map_sub]
      exact (show ‖ofPolynomial A x - ofPolynomial A qr.2‖ ≤
          max ‖ofPolynomial A x‖ ‖ofPolynomial A qr.2‖ from by
        simpa only [sub_eq_add_neg, norm_neg] using
          IsUltrametricDist.norm_add_le_max
            (ofPolynomial A x) (-(ofPolynomial A qr.2))).trans
        (max_le hxnorm (hrnorm.trans hxnorm))
    simpa only [coeff_ofPolynomial] using
      (norm_le_iff A (ofPolynomial A w) zero_le_one).mp hwnorm
  have hfactor : f = ((u⁻¹ : (Algebra A)ˣ) : Algebra A) * ofPolynomial A w := by
    rw [hwval, ← hu, mul_comm f (u : Algebra A), ← mul_assoc]
    simp
  refine ⟨(u⁻¹, w), ⟨hfactor, hw, hwd, hwcoeff⟩, ?_⟩
  rintro ⟨e', w'⟩ ⟨hfactor', hw', hwd', _⟩
  have hr' : (x - w').degree < d := degree_X_pow_sub_monic_lt w' hw' d hwd'
  have heq' : ofPolynomial A x =
      f * ((e'⁻¹ : (Algebra A)ˣ) : Algebra A) + ofPolynomial A (x - w') := by
    rw [hfactor', map_sub]
    simp [mul_left_comm, mul_comm]
  have hb := norm_le_normalizedDistinguished_mul_add f d hf
    ((e'⁻¹ : (Algebra A)ˣ) : Algebra A) (x - w') hr'
  rw [← heq'] at hb
  have hpair := huniq
    (((e'⁻¹ : (Algebra A)ˣ) : Algebra A), x - w') ⟨heq', hr', hb.1, hb.2⟩
  have he' : e'⁻¹ = u := by
    apply Units.ext
    exact (congrArg Prod.fst hpair).trans hu.symm
  have hw'eq : w' = w := by
    have ht := congrArg Prod.snd hpair
    dsimp only at ht
    dsimp [w]
    linear_combination -ht
  exact Prod.ext (by simpa using congrArg Inv.inv he') hw'eq

end Langlands.Analytic.RestrictedSeries
