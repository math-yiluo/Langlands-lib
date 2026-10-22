import Langlands.Geometry.Analytic.MonicSeriesDivision
import Mathlib.Topology.MetricSpace.Contracting

/-! # Analytic division by a strictly small perturbation of a monic polynomial -/

noncomputable section

universe u

namespace Langlands.Analytic.RestrictedSeries

open Polynomial

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]
  [Nontrivial A] [CompleteSpace A]

/-- The quotient and remainder constructed by monic analytic division. -/
def monicDivision (p : Polynomial A) (hp : p.Monic)
    (hunit : ∀ n, ‖p.coeff n‖ ≤ 1) (f : Algebra A) :
    Algebra A × Polynomial A :=
  (existsUnique_monic_division p hp hunit f).exists.choose

theorem monicDivision_spec (p : Polynomial A) (hp : p.Monic)
    (hunit : ∀ n, ‖p.coeff n‖ ≤ 1) (f : Algebra A) :
    f = ofPolynomial A p * (monicDivision p hp hunit f).1 +
        ofPolynomial A (monicDivision p hp hunit f).2 ∧
    (monicDivision p hp hunit f).2.degree < p.degree ∧
    ‖(monicDivision p hp hunit f).1‖ ≤ ‖f‖ ∧
    ‖ofPolynomial A (monicDivision p hp hunit f).2‖ ≤ ‖f‖ :=
  (existsUnique_monic_division p hp hunit f).exists.choose_spec

theorem monicDivision_quotient_dist_le (p : Polynomial A) (hp : p.Monic)
    (hunit : ∀ n, ‖p.coeff n‖ ≤ 1) (f g : Algebra A) :
    dist (monicDivision p hp hunit f).1 (monicDivision p hp hunit g).1 ≤ dist f g := by
  obtain ⟨hf, hdf, _, _⟩ := monicDivision_spec p hp hunit f
  obtain ⟨hg, hdg, _, _⟩ := monicDivision_spec p hp hunit g
  have hd : ((monicDivision p hp hunit f).2 -
      (monicDivision p hp hunit g).2).degree < p.degree :=
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt hdf hdg)
  have h := (norm_le_monic_mul_add p hp hunit
    ((monicDivision p hp hunit f).1 - (monicDivision p hp hunit g).1)
    ((monicDivision p hp hunit f).2 - (monicDivision p hp hunit g).2) hd).1
  rw [map_sub, mul_sub] at h
  rw [show ofPolynomial A p * (monicDivision p hp hunit f).1 -
        ofPolynomial A p * (monicDivision p hp hunit g).1 +
        (ofPolynomial A (monicDivision p hp hunit f).2 -
          ofPolynomial A (monicDivision p hp hunit g).2) =
      (ofPolynomial A p * (monicDivision p hp hunit f).1 +
        ofPolynomial A (monicDivision p hp hunit f).2) -
      (ofPolynomial A p * (monicDivision p hp hunit g).1 +
        ofPolynomial A (monicDivision p hp hunit g).2) by abel,
    ← hf, ← hg] at h
  simpa only [dist_eq_norm] using h

/-- The quotient-solving map is an actual contraction, with constant the norm
of the perturbation. -/
theorem division_contraction (p : Polynomial A) (hp : p.Monic)
    (hunit : ∀ n, ‖p.coeff n‖ ≤ 1) (h : Algebra A) (hh : ‖h‖ < 1)
    (f : Algebra A) :
    ContractingWith ‖h‖₊ (fun q => (monicDivision p hp hunit (f - h * q)).1) := by
  refine ⟨by exact_mod_cast hh, LipschitzWith.of_dist_le_mul fun q q' => ?_⟩
  apply (monicDivision_quotient_dist_le p hp hunit (f - h * q) (f - h * q')).trans
  rw [dist_eq_norm, show f - h * q - (f - h * q') = h * (q' - q) by ring]
  rw [dist_eq_norm]
  change ‖h * (q' - q)‖ ≤ ‖h‖ * ‖q - q'‖
  simpa only [norm_sub_rev] using
    norm_mul_le h (q' - q)

/-- Analytic division by a monic unit-ball polynomial plus a series of norm
strictly below one. The fixed point is constructed by the contraction theorem. -/
theorem exists_perturbed_monic_division
    (p : Polynomial A) (hp : p.Monic) (hunit : ∀ n, ‖p.coeff n‖ ≤ 1)
    (h : Algebra A) (hh : ‖h‖ < 1) (f : Algebra A) :
    ∃ q : Algebra A, ∃ r : Polynomial A,
      f = (ofPolynomial A p + h) * q + ofPolynomial A r ∧
      r.degree < p.degree ∧ ‖q‖ ≤ ‖f‖ ∧ ‖ofPolynomial A r‖ ≤ ‖f‖ := by
  let T := fun q => (monicDivision p hp hunit (f - h * q)).1
  have hT : ContractingWith ‖h‖₊ T := division_contraction p hp hunit h hh f
  let q := hT.fixedPoint T
  have hqfix : (monicDivision p hp hunit (f - h * q)).1 = q :=
    hT.fixedPoint_isFixedPt
  let r := (monicDivision p hp hunit (f - h * q)).2
  obtain ⟨heq, hdegree, hqnorm, hrnorm⟩ := monicDivision_spec p hp hunit (f - h * q)
  rw [hqfix] at heq hqnorm
  have hdiff : ‖f - h * q‖ ≤ max ‖f‖ (‖h‖ * ‖q‖) :=
    (show ‖f - h * q‖ ≤ max ‖f‖ ‖h * q‖ from by
      simpa only [sub_eq_add_neg, norm_neg] using
        IsUltrametricDist.norm_add_le_max f (-(h * q))).trans
      (max_le_max le_rfl (norm_mul_le _ _))
  have hqbound : ‖q‖ ≤ ‖f‖ := by
    by_contra hn
    have hlt : ‖f‖ < ‖q‖ := lt_of_not_ge hn
    have hpos : 0 < ‖q‖ := lt_of_le_of_lt (norm_nonneg f) hlt
    have hc : ‖h‖ * ‖q‖ < ‖q‖ := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hh hpos
    exact (not_lt_of_ge (hqnorm.trans hdiff)) (max_lt hlt hc)
  have hsmall : ‖h‖ * ‖q‖ ≤ ‖f‖ :=
    (mul_le_of_le_one_left (norm_nonneg q) hh.le).trans hqbound
  refine ⟨q, r, ?_, hdegree, hqbound, hrnorm.trans (hdiff.trans (max_le le_rfl hsmall))⟩
  change f = (ofPolynomial A p + h) * q +
    ofPolynomial A (monicDivision p hp hunit (f - h * q)).2
  calc
    f = (ofPolynomial A p * q +
      ofPolynomial A (monicDivision p hp hunit (f - h * q)).2) + h * q :=
      sub_eq_iff_eq_add.mp heq
    _ = _ := by ring

/-- The analytic division decomposition for a strictly small perturbation is
unique, with the same norm bounds as polynomial division. -/
theorem existsUnique_perturbed_monic_division
    (p : Polynomial A) (hp : p.Monic) (hunit : ∀ n, ‖p.coeff n‖ ≤ 1)
    (h : Algebra A) (hh : ‖h‖ < 1) (f : Algebra A) :
    ∃! qr : Algebra A × Polynomial A,
      f = (ofPolynomial A p + h) * qr.1 + ofPolynomial A qr.2 ∧
      qr.2.degree < p.degree ∧ ‖qr.1‖ ≤ ‖f‖ ∧
      ‖ofPolynomial A qr.2‖ ≤ ‖f‖ := by
  obtain ⟨q, r, heq, hdegree, hq, hr⟩ :=
    exists_perturbed_monic_division p hp hunit h hh f
  refine ⟨(q, r), ⟨heq, hdegree, hq, hr⟩, ?_⟩
  rintro ⟨q', r'⟩ ⟨heq', hdegree', _, _⟩
  have hd : (r' - r).degree < p.degree :=
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt hdegree' hdegree)
  have he : ofPolynomial A p * (q' - q) + ofPolynomial A (r' - r) =
      -(h * (q' - q)) := by
    calc
      _ = ((ofPolynomial A p + h) * q' + ofPolynomial A r') -
        ((ofPolynomial A p + h) * q + ofPolynomial A r) - h * (q' - q) := by
          rw [map_sub]
          ring
      _ = _ := by rw [← heq', ← heq, sub_self, zero_sub]
  have hest := norm_le_monic_mul_add p hp hunit (q' - q) (r' - r) hd
  rw [he, norm_neg] at hest
  have hqzero : q' - q = 0 := by
    by_contra hn
    have hpos := norm_pos_iff.mpr hn
    have hc : ‖h‖ * ‖q' - q‖ < ‖q' - q‖ := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hh hpos
    exact (not_lt_of_ge (hest.1.trans (norm_mul_le _ _))) hc
  have hrzero : ofPolynomial A (r' - r) = 0 := by
    simpa only [hqzero, mul_zero, norm_zero, norm_le_zero_iff] using hest.2
  refine Prod.ext (sub_eq_zero.mp hqzero) ?_
  apply ofPolynomial_injective A
  exact sub_eq_zero.mp (by simpa only [map_sub] using hrzero)

end Langlands.Analytic.RestrictedSeries
