import Langlands.Geometry.Analytic.TateRegrouping
import Langlands.Geometry.Analytic.DistinguishedNormalization
import Langlands.Geometry.Analytic.WeierstrassQuotient
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Norm bounds and primality for Weierstrass polynomial factors -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_ungroup {n : ℕ}
    (f : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) :
    ‖ungroup f‖ = ‖f‖ := by
  simpa only [regroup_ungroup] using (norm_regroup (ungroup f)).symm

/-- The actual regrouping transfers the proved finite-variable Gauss
multiplicativity to restricted series over a smaller Tate algebra. -/
theorem norm_mul_regrouped (n : ℕ)
    (f g : RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) :
    ‖f * g‖ = ‖f‖ * ‖g‖ := by
  calc
    ‖f * g‖ = ‖(regroupEquiv n).symm (f * g)‖ := (norm_ungroup _).symm
    _ = ‖(regroupEquiv n).symm f * (regroupEquiv n).symm g‖ := by
      rw [map_mul]
    _ = ‖(regroupEquiv n).symm f‖ * ‖(regroupEquiv n).symm g‖ := norm_mul _ _
    _ = ‖f‖ * ‖g‖ := by
      change ‖ungroup f‖ * ‖ungroup g‖ = _
      rw [norm_ungroup, norm_ungroup]

/-- Both monic factors of a monic unit-ball polynomial over a smaller Tate
algebra again have unit-ball coefficients. This is derived from the actual
Gauss norm, not imposed as a closure axiom for a polynomial class. -/
theorem monic_factors_coeff_le_one (n : ℕ)
    (p q : Polynomial (StrictTateAlgebra (Fin n) K)) (hp : p.Monic) (hq : q.Monic)
    (hpq : ∀ i, ‖(p * q).coeff i‖ ≤ 1) :
    (∀ i, ‖p.coeff i‖ ≤ 1) ∧ (∀ i, ‖q.coeff i‖ ≤ 1) := by
  let A := StrictTateAlgebra (Fin n) K
  have hpone : 1 ≤ ‖RestrictedSeries.ofPolynomial A p‖ := by
    have h := ((RestrictedSeries.norm_le_iff A _ (norm_nonneg _)).mp
      (le_rfl : ‖RestrictedSeries.ofPolynomial A p‖ ≤
        ‖RestrictedSeries.ofPolynomial A p‖)) p.natDegree
    simpa only [RestrictedSeries.coeff_ofPolynomial, hp.coeff_natDegree, norm_one] using h
  have hqone : 1 ≤ ‖RestrictedSeries.ofPolynomial A q‖ := by
    have h := ((RestrictedSeries.norm_le_iff A _ (norm_nonneg _)).mp
      (le_rfl : ‖RestrictedSeries.ofPolynomial A q‖ ≤
        ‖RestrictedSeries.ofPolynomial A q‖)) q.natDegree
    simpa only [RestrictedSeries.coeff_ofPolynomial, hq.coeff_natDegree, norm_one] using h
  have hprod : ‖RestrictedSeries.ofPolynomial A p‖ *
      ‖RestrictedSeries.ofPolynomial A q‖ ≤ 1 := by
    rw [← norm_mul_regrouped, ← map_mul]
    apply (RestrictedSeries.norm_le_iff A _ zero_le_one).mpr
    simpa only [RestrictedSeries.coeff_ofPolynomial] using hpq
  have hpbound : ‖RestrictedSeries.ofPolynomial A p‖ ≤ 1 :=
    (le_mul_of_one_le_right (norm_nonneg _) hqone).trans hprod
  have hqbound : ‖RestrictedSeries.ofPolynomial A q‖ ≤ 1 :=
    (le_mul_of_one_le_left (norm_nonneg _) hpone).trans hprod
  constructor
  · simpa only [RestrictedSeries.coeff_ofPolynomial] using
      (RestrictedSeries.norm_le_iff A _ zero_le_one).mp hpbound
  · simpa only [RestrictedSeries.coeff_ofPolynomial] using
      (RestrictedSeries.norm_le_iff A _ zero_le_one).mp hqbound

end Langlands.Analytic.StrictTateAlgebra

namespace Langlands.Analytic.RestrictedSeries

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]
  [Nontrivial A] [CompleteSpace A]

/-- A prime monic unit-ball polynomial remains prime in the actual analytic
ring, because the constructed quotient equivalence transports its domain. -/
theorem prime_ofPolynomial
    (w : Polynomial A) (hw : w.Monic) (hunit : ∀ n, ‖w.coeff n‖ ≤ 1)
    (hprime : Prime w) : Prime (ofPolynomial A w) := by
  let : (Ideal.span {w}).IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
  have hdom : IsDomain (Algebra A ⧸ Ideal.span {ofPolynomial A w}) :=
    (weierstrassQuotientEquiv w hw hunit).toRingEquiv.toMulEquiv.isDomain_iff.mp
      inferInstance
  have hprim : (Ideal.span {ofPolynomial A w}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  apply (Ideal.span_singleton_prime ?_).mp hprim
  intro hzero
  apply hprime.ne_zero
  apply ofPolynomial_injective A
  simpa only [map_zero] using hzero

end Langlands.Analytic.RestrictedSeries
