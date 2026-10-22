import Langlands.Geometry.Analytic.TatePolynomial
import Langlands.Geometry.Analytic.PolynomialDivision
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Division of convergent series by monic unit-ball polynomials -/

noncomputable section

universe u

namespace Langlands.Analytic.RestrictedSeries

open Filter Polynomial
open scoped Topology

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]

private theorem polynomial_division_dist_le
    (p : Polynomial A) (hp : p.Monic) (hunit : ∀ n, ‖p.coeff n‖ ≤ 1)
    (f g : Polynomial A) :
    dist (ofPolynomial A (f /ₘ p)) (ofPolynomial A (g /ₘ p)) ≤
      dist (ofPolynomial A f) (ofPolynomial A g) ∧
    dist (ofPolynomial A (f %ₘ p)) (ofPolynomial A (g %ₘ p)) ≤
      dist (ofPolynomial A f) (ofPolynomial A g) := by
  simp only [dist_eq_norm, ← map_sub, norm_ofPolynomial,
    ← Polynomial.sub_divByMonic, ← Polynomial.sub_modByMonic]
  exact polynomial_division_supNorm_le (f - g) p hp hunit

private theorem division_cauchy
    (p : Polynomial A) (hp : p.Monic) (hunit : ∀ n, ‖p.coeff n‖ ≤ 1)
    (f : Algebra A) :
    CauchySeq (fun n => ofPolynomial A (trunc A n f /ₘ p)) ∧
    CauchySeq (fun n => ofPolynomial A (trunc A n f %ₘ p)) := by
  have hf := Metric.cauchySeq_iff.mp (tendsto_trunc A f).cauchySeq
  constructor
  all_goals
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
  · exact lt_of_le_of_lt
      (polynomial_division_dist_le p hp hunit (trunc A m f) (trunc A n f)).1
      (hN m hm n hn)
  · exact lt_of_le_of_lt
      (polynomial_division_dist_le p hp hunit (trunc A m f) (trunc A n f)).2
      (hN m hm n hn)

/-- A restricted series with no coefficients in degrees at least `d` is its
actual polynomial truncation. -/
theorem ofPolynomial_trunc_eq (d : ℕ) (f : Algebra A)
    (hf : ∀ n, d ≤ n → coeff A n f = 0) :
    ofPolynomial A (trunc A d f) = f := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  change coeff A n (ofPolynomial A (trunc A d f)) = coeff A n f
  rw [coeff_ofPolynomial, coeff_trunc]
  split_ifs with hn
  · rfl
  · exact (hf n (Nat.le_of_not_gt hn)).symm

/-- The sharp polynomial division estimates persist when the quotient is
an arbitrary restricted series and the remainder has degree below the divisor. -/
theorem norm_le_monic_mul_add
    (p : Polynomial A) (hp : p.Monic) (hunit : ∀ n, ‖p.coeff n‖ ≤ 1)
    (q : Algebra A) (r : Polynomial A) (hr : r.degree < p.degree) :
    ‖q‖ ≤ ‖ofPolynomial A p * q + ofPolynomial A r‖ ∧
    ‖ofPolynomial A r‖ ≤ ‖ofPolynomial A p * q + ofPolynomial A r‖ := by
  have hq := tendsto_trunc A q
  have hsum := ((tendsto_const_nhds (x := ofPolynomial A p)).mul hq).add
    (tendsto_const_nhds (x := ofPolynomial A r))
  have hest (n : ℕ) :
      ‖ofPolynomial A (trunc A n q)‖ ≤
        ‖ofPolynomial A p * ofPolynomial A (trunc A n q) + ofPolynomial A r‖ ∧
      ‖ofPolynomial A r‖ ≤
        ‖ofPolynomial A p * ofPolynomial A (trunc A n q) + ofPolynomial A r‖ := by
    have hu := Polynomial.div_modByMonic_unique (trunc A n q) r hp
      ⟨rfl, hr⟩
    have he := polynomial_division_supNorm_le (r + p * trunc A n q) p hp hunit
    rw [hu.1, hu.2] at he
    simpa only [← map_mul, ← map_add, norm_ofPolynomial, add_comm] using he
  exact ⟨le_of_tendsto_of_tendsto' hq.norm hsum.norm (fun n => (hest n).1),
    le_of_tendsto_of_tendsto' tendsto_const_nhds hsum.norm (fun n => (hest n).2)⟩

variable [Nontrivial A] [CompleteSpace A]

/-- Analytic division by an actual monic unit-ball polynomial. The quotient
is a convergent series, and the remainder is an actual polynomial of smaller
degree. Both have norm at most the dividend's norm. -/
theorem exists_monic_division
    (p : Polynomial A) (hp : p.Monic) (hunit : ∀ n, ‖p.coeff n‖ ≤ 1)
    (f : Algebra A) :
    ∃ q : Algebra A, ∃ r : Polynomial A,
      f = ofPolynomial A p * q + ofPolynomial A r ∧
      r.degree < p.degree ∧ ‖q‖ ≤ ‖f‖ ∧ ‖ofPolynomial A r‖ ≤ ‖f‖ := by
  obtain ⟨hqC, hrC⟩ := division_cauchy p hp hunit f
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hqC
  obtain ⟨r, hr⟩ := cauchySeq_tendsto_of_complete hrC
  have htail : ∀ n, p.natDegree ≤ n → coeff A n r = 0 := by
    intro n hn
    have hc := (coeff A n).continuous.tendsto r |>.comp hr
    have heq : ∀ m, coeff A n (ofPolynomial A (trunc A m f %ₘ p)) = 0 := by
      intro m
      rw [coeff_ofPolynomial]
      apply Polynomial.coeff_eq_zero_of_degree_lt
      exact (Polynomial.degree_modByMonic_lt _ hp).trans_le
        (Polynomial.degree_le_natDegree.trans (by exact_mod_cast hn))
    exact tendsto_nhds_unique hc (by simpa only [Function.comp_def, heq] using
      (tendsto_const_nhds (x := (0 : A)) : Tendsto (fun _ : ℕ => (0 : A)) atTop (𝓝 0)))
  let rpoly := trunc A p.natDegree r
  have hrpoly : ofPolynomial A rpoly = r := ofPolynomial_trunc_eq p.natDegree r htail
  have hdegree : rpoly.degree < p.degree := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]
    exact PowerSeries.degree_trunc_lt r.val p.natDegree
  have hsum := ((tendsto_const_nhds (x := ofPolynomial A p)).mul hq).add hr
  have heq (n : ℕ) :
      ofPolynomial A p * ofPolynomial A (trunc A n f /ₘ p) +
          ofPolynomial A (trunc A n f %ₘ p) =
        ofPolynomial A (trunc A n f) := by
    rw [← map_mul, ← map_add]
    congr 1
    simpa only [add_comm] using Polynomial.modByMonic_add_div (trunc A n f) p
  have hdivision : f = ofPolynomial A p * q + r :=
    tendsto_nhds_unique (tendsto_trunc A f) (by simpa only [heq] using hsum)
  refine ⟨q, rpoly, by simpa only [hrpoly] using hdivision, hdegree, ?_⟩
  rw [hdivision, ← hrpoly]
  exact norm_le_monic_mul_add p hp hunit q rpoly hdegree

/-- Unique analytic division, including its sharp norm bounds, follows from
the actual limiting construction and the lower bounds for multiplication. -/
theorem existsUnique_monic_division
    (p : Polynomial A) (hp : p.Monic) (hunit : ∀ n, ‖p.coeff n‖ ≤ 1)
    (f : Algebra A) :
    ∃! qr : Algebra A × Polynomial A,
      f = ofPolynomial A p * qr.1 + ofPolynomial A qr.2 ∧
      qr.2.degree < p.degree ∧ ‖qr.1‖ ≤ ‖f‖ ∧ ‖ofPolynomial A qr.2‖ ≤ ‖f‖ := by
  obtain ⟨q, r, hdivision, hdegree, hq, hr⟩ := exists_monic_division p hp hunit f
  refine ⟨(q, r), ⟨hdivision, hdegree, hq, hr⟩, ?_⟩
  rintro ⟨q', r'⟩ ⟨hdivision', hdegree', _, _⟩
  have hd : (r' - r).degree < p.degree :=
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt hdegree' hdegree)
  have hzero : ofPolynomial A p * (q' - q) + ofPolynomial A (r' - r) = 0 := by
    rw [map_sub, mul_sub]
    rw [show ofPolynomial A p * q' - ofPolynomial A p * q +
        (ofPolynomial A r' - ofPolynomial A r) =
      (ofPolynomial A p * q' + ofPolynomial A r') -
        (ofPolynomial A p * q + ofPolynomial A r) by abel]
    rw [← hdivision', ← hdivision, sub_self]
  have hest := norm_le_monic_mul_add p hp hunit (q' - q) (r' - r) hd
  rw [hzero, norm_zero] at hest
  have hqeq : q' = q := sub_eq_zero.mp (norm_le_zero_iff.mp hest.1)
  have hreq : r' = r := by
    apply ofPolynomial_injective A
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact norm_le_zero_iff.mp hest.2
  exact Prod.ext hqeq hreq

end Langlands.Analytic.RestrictedSeries
