import Langlands.Geometry.Analytic.MonicSeriesDivision
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Polynomial and analytic quotients by a Weierstrass polynomial -/

noncomputable section

universe u

namespace Langlands.Analytic.RestrictedSeries

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]
  [Nontrivial A]

/-- Divisibility of polynomials by a monic unit-ball polynomial is unchanged
after passing to actual restricted series. Analytic uniqueness forces the
ordinary polynomial remainder to vanish. -/
theorem ofPolynomial_dvd_iff
    (w : Polynomial A) (hw : w.Monic) (hunit : ∀ n, ‖w.coeff n‖ ≤ 1)
    (p : Polynomial A) :
    ofPolynomial A w ∣ ofPolynomial A p ↔ w ∣ p := by
  constructor
  · rintro ⟨q, hq⟩
    have hsum : ofPolynomial A w * (ofPolynomial A (p /ₘ w) - q) +
        ofPolynomial A (p %ₘ w) = 0 := by
      rw [Polynomial.modByMonic_eq_sub_mul_div, map_sub, map_mul, hq]
      ring
    have hbound := (norm_le_monic_mul_add w hw hunit
      (ofPolynomial A (p /ₘ w) - q) (p %ₘ w)
      (Polynomial.degree_modByMonic_lt p hw)).2
    rw [hsum, norm_zero] at hbound
    have hrzero : ofPolynomial A (p %ₘ w) = 0 :=
      norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
    apply (Polynomial.modByMonic_eq_zero_iff_dvd hw).mp
    apply ofPolynomial_injective A
    simpa only [map_zero] using hrzero
  · exact fun hp => map_dvd (ofPolynomial A) hp

theorem ofPolynomial_mem_span_iff
    (w : Polynomial A) (hw : w.Monic) (hunit : ∀ n, ‖w.coeff n‖ ≤ 1)
    (p : Polynomial A) :
    ofPolynomial A p ∈ Ideal.span {ofPolynomial A w} ↔
      p ∈ Ideal.span {w} := by
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact ofPolynomial_dvd_iff w hw hunit p

/-- The actual map of principal-ideal quotients induced by polynomial
inclusion. Its definition requires no division or bijectivity assumption. -/
def weierstrassQuotientMap (w : Polynomial A) :
    Polynomial A ⧸ Ideal.span {w} →ₐ[A]
      Algebra A ⧸ Ideal.span {ofPolynomial A w} :=
  Ideal.quotientMapₐ _ (ofPolynomial A) (by
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = w := Set.mem_singleton_iff.mp hp
    subst p
    exact Ideal.subset_span (Set.mem_singleton _))

theorem weierstrassQuotientMap_injective
    (w : Polynomial A) (hw : w.Monic) (hunit : ∀ n, ‖w.coeff n‖ ≤ 1) :
    Function.Injective (weierstrassQuotientMap w) := by
  apply (injective_iff_map_eq_zero (weierstrassQuotientMap w).toRingHom).mpr
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (ofPolynomial_mem_span_iff w hw hunit p).mp
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

variable [CompleteSpace A]

theorem weierstrassQuotientMap_surjective
    (w : Polynomial A) (hw : w.Monic) (hunit : ∀ n, ‖w.coeff n‖ ≤ 1) :
    Function.Surjective (weierstrassQuotientMap w) := by
  intro y
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q, r, hg, _, _, _⟩ := exists_monic_division w hw hunit g
  refine ⟨Ideal.Quotient.mk _ r, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {ofPolynomial A w}) (ofPolynomial A r) =
    Ideal.Quotient.mk (Ideal.span {ofPolynomial A w}) g
  have hwzero : Ideal.Quotient.mk (Ideal.span {ofPolynomial A w})
      (ofPolynomial A w) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hg, map_add, map_mul, hwzero, zero_mul, zero_add]

/-- The polynomial quotient is genuinely isomorphic to the restricted-series
quotient. Both inverse-existence obligations are proved by analytic division. -/
def weierstrassQuotientEquiv
    (w : Polynomial A) (hw : w.Monic) (hunit : ∀ n, ‖w.coeff n‖ ≤ 1) :
    (Polynomial A ⧸ Ideal.span {w}) ≃ₐ[A]
      (Algebra A ⧸ Ideal.span {ofPolynomial A w}) :=
  AlgEquiv.ofBijective (weierstrassQuotientMap w)
    ⟨weierstrassQuotientMap_injective w hw hunit,
      weierstrassQuotientMap_surjective w hw hunit⟩

end Langlands.Analytic.RestrictedSeries
