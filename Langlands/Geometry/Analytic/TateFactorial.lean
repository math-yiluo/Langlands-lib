import Langlands.Geometry.Analytic.TateNoetherian
import Langlands.Geometry.Analytic.TateWeierstrassFactors
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-! # Unique factorization in actual finite-variable Tate algebras -/

noncomputable section

universe u

namespace Langlands.Analytic

/-- A nonunit monic polynomial over a unique factorization domain has a
monic prime factor and a monic complementary factor. The leading unit is
constructed from their actual leading-coefficient product. -/
theorem exists_monic_prime_factor {R : Type u} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (w : Polynomial R)
    (hw : w.Monic) (hunit : ¬ IsUnit w) :
    ∃ p q : Polynomial R, p.Monic ∧ q.Monic ∧ Prime p ∧ w = p * q := by
  obtain ⟨p, hp, hpw⟩ := WfDvdMonoid.exists_irreducible_factor hunit hw.ne_zero
  obtain ⟨q, hpq⟩ := hpw
  have hlc : p.leadingCoeff * q.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul, ← hpq, hw.leadingCoeff]
  let a : Rˣ :=
    { val := p.leadingCoeff
      inv := q.leadingCoeff
      val_inv := hlc
      inv_val := by simpa only [mul_comm] using hlc }
  let p' := Polynomial.C ((a⁻¹ : Rˣ) : R) * p
  let q' := Polynomial.C (a : R) * q
  have hp'monic : p'.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    change ((a⁻¹ : Rˣ) : R) * (a : R) = 1
    exact a.inv_val
  have hfactor : w = p' * q' := by
    calc
      w = p * q := hpq
      _ = (Polynomial.C ((a⁻¹ : Rˣ) : R) * Polynomial.C (a : R)) * (p * q) := by
        rw [← Polynomial.C_mul]
        simp
      _ = p' * q' := by dsimp [p', q']; ring
  have hq'monic : q'.Monic :=
    hp'monic.of_mul_monic_left (hfactor ▸ hw)
  have hassoc : Associated p' p :=
    associated_unit_mul_left p _ ((a⁻¹).isUnit.map Polynomial.C)
  have hp'prime : Prime p' :=
    hassoc.prime_iff.mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp)
  exact ⟨p', q', hp'monic, hq'monic, hp'prime, hfactor⟩

namespace StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The actual restricted subalgebra inherits the domain structure from
formal power series over the coefficient field. -/
instance (n : ℕ) : IsDomain (StrictTateAlgebra (Fin n) K) := by
  let : NoZeroDivisors (StrictTateAlgebra (Fin n) K) :=
    inferInstanceAs (NoZeroDivisors ↥(restrictedSubalgebra (Fin n) K))
  exact NoZeroDivisors.to_isDomain _

/-- Unique factorization follows by the actual coordinate/preparation
construction, monic polynomial factorization over the smaller Tate algebra,
and the proved polynomial/analytic quotient equivalence. -/
theorem uniqueFactorization_tate (n : ℕ) :
    UniqueFactorizationMonoid (StrictTateAlgebra (Fin n) K) := by
  induction n with
  | zero =>
    let e := RingEquiv.ofBijective (algebraMap K (StrictTateAlgebra (Fin 0) K))
      ⟨(algebraMap K (StrictTateAlgebra (Fin 0) K)).injective,
        zeroVariables_algebraMap_surjective⟩
    exact e.toMulEquiv.uniqueFactorizationMonoid inferInstance
  | succ n ih =>
    let := ih
    let : IsDomain (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) :=
      (MulEquiv.isDomain_iff (regroupEquiv (A := K) n).toMulEquiv).mp inferInstance
    refine
      { toIsCancelMulZero := inferInstance
        toWellFounded := inferInstance
        irreducible_iff_prime := ?_ }
    intro f
    refine ⟨fun hf => ?_, Prime.irreducible⟩
    obtain ⟨φ, _, d, hdist⟩ := exists_distinguished_coordinateChange n f hf.ne_zero
    let e := φ.toRingEquiv.trans (regroupEquiv n)
    have he_irred : Irreducible (e f) := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hf
    obtain ⟨⟨a, w⟩, hprep, _⟩ :=
      RestrictedSeries.existsUnique_distinguished_preparation
        (regroupEquiv n (φ f)) d hdist
    have hassoc : Associated (e f) (RestrictedSeries.ofPolynomial _ w) := by
      change Associated (regroupEquiv n (φ f)) _
      rw [hprep.1]
      exact associated_unit_mul_left _ _ a.isUnit
    have hw_irred : Irreducible (RestrictedSeries.ofPolynomial _ w) :=
      hassoc.irreducible_iff.mp he_irred
    have hwunit : ¬ IsUnit w := by
      intro h
      exact hw_irred.not_isUnit (h.map (RestrictedSeries.ofPolynomial _))
    obtain ⟨p, q, hp, hq, hprime, hfactor⟩ :=
      exists_monic_prime_factor w hprep.2.1 hwunit
    have hpbound : ∀ i, ‖p.coeff i‖ ≤ 1 :=
      (monic_factors_coeff_le_one n p q hp hq (by
        rw [← hfactor]
        exact hprep.2.2.2)).1
    have hpprime : Prime (RestrictedSeries.ofPolynomial _ p) :=
      RestrictedSeries.prime_ofPolynomial p hp hpbound hprime
    have hpdiv : RestrictedSeries.ofPolynomial _ p ∣
        RestrictedSeries.ofPolynomial _ w :=
      map_dvd (RestrictedSeries.ofPolynomial _) ⟨q, hfactor⟩
    have hpwassoc : Associated (RestrictedSeries.ofPolynomial _ p)
        (RestrictedSeries.ofPolynomial _ w) :=
      (hpprime.irreducible.dvd_irreducible_iff_associated hw_irred).mp hpdiv
    have hwprime : Prime (RestrictedSeries.ofPolynomial _ w) :=
      hpwassoc.prime_iff.mp hpprime
    exact (MulEquiv.prime_iff e.toMulEquiv).mp (hassoc.prime_iff.mpr hwprime)

instance (n : ℕ) : UniqueFactorizationMonoid (StrictTateAlgebra (Fin n) K) :=
  uniqueFactorization_tate n

end StrictTateAlgebra

end Langlands.Analytic
