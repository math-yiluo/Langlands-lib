import Langlands.Geometry.Analytic.PrimeQuotientSpectralRelation
import Langlands.Geometry.Analytic.AffinoidPowerBounds
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # Spectral inequalities give bounded powers in every presented affinoid -/

noncomputable section

open scoped BigOperators

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

section NontrivialValuation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- In the nontrivially valued case, multiply the constructed relations
for the finitely many minimal primes and kill the nilpotent value by
taking a power. Every coefficient remains in the original Tate unit ball. -/
theorem exists_monic_norm_le_one_relation
    (P : PresentedStrictAffinoidAlgebra K)
    (a : P) (ha : ∀ x : BanachSpectrum P, x a ≤ 1) :
    ∃ p : Polynomial (StrictTateAlgebra (Fin P.arity) K),
      p.Monic ∧ (∀ i, ‖p.coeff i‖ ≤ 1) ∧
      p.eval₂ (presentationMap K P).toAlgHom.toRingHom a = 0 := by
  classical
  let T := StrictTateAlgebra (Fin P.arity) K
  let S := normUnitBallSubring T
  let J := minimalPrimes P
  let _ : Fintype J := (minimalPrimes.finite_of_isNoetherianRing P).fintype
  have hrel : ∀ I : J, ∃ p : Polynomial T,
      p.Monic ∧ (∀ i, ‖p.coeff i‖ ≤ 1) ∧
      p.eval₂ (presentationMap K P).toAlgHom.toRingHom a ∈ I.val := by
    intro I
    let _ : I.val.IsPrime := I.property.isPrime
    exact exists_monic_relation_mem_prime P I.val a ha
  choose p hp hc hm using hrel
  let r : Polynomial T := ∏ I : J, p I
  have hr : r.Monic := Polynomial.monic_prod_of_monic _ _ fun I _ => hp I
  have hlift : r ∈ Polynomial.lifts S.subtype := by
    apply (Polynomial.lifts S.subtype).prod_mem
    intro I _
    apply (Polynomial.lifts_iff_coeff_lifts (p I)).mpr
    intro i
    exact ⟨⟨(p I).coeff i, hc I i⟩, rfl⟩
  have hrad :
      r.eval₂ (presentationMap K P).toAlgHom.toRingHom a ∈ (⊥ : Ideal P).radical := by
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro I hI
    change (∏ j : J, p j).eval₂ _ a ∈ I
    rw [Polynomial.eval₂_finsetProd]
    exact I.prod_mem (Finset.mem_univ (⟨I, hI⟩ : J)) (hm ⟨I, hI⟩)
  obtain ⟨e, he⟩ := hrad
  refine ⟨r ^ e, hr.pow e, ?_, ?_⟩
  · intro i
    obtain ⟨c, hceq⟩ :=
      (Polynomial.lifts_iff_coeff_lifts (r ^ e)).mp
        ((Polynomial.lifts S.subtype).pow_mem hlift e) i
    rw [← hceq]
    exact c.property
  · rw [Polynomial.eval₂_pow]
    exact he

end NontrivialValuation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The full spectral bound for genuine presented strict affinoid quotients,
including nonreduced and zero quotients and trivially valued fields. -/
theorem hasBoundedPowers_of_spectrum_le_one
    (P : PresentedStrictAffinoidAlgebra K)
    (a : P) (ha : ∀ x : BanachSpectrum P, x a ≤ 1) :
    HasBoundedPowers a := by
  by_cases hK : ∀ c : K, ‖c‖ ≤ 1
  · exact hasBoundedPowers_of_scalar_norm_le_one P hK a
  push Not at hK
  let _ : NontriviallyNormedField K :=
    { toNormedField := inferInstance, non_trivial := hK }
  obtain ⟨p, hp, hc, he⟩ := exists_monic_norm_le_one_relation P a ha
  exact hasBoundedPowers_of_tate_monic_relation (presentationMap K P) a p hp he hc

/-- The closing theorem inhabits the whole original proposition. -/
theorem spectralPowerBound : SpectralPowerBoundStatement K :=
  hasBoundedPowers_of_spectrum_le_one

/-- The spectral criterion in both directions; the reverse direction
already holds in every normed commutative ring. -/
theorem hasBoundedPowers_iff_spectrum_le_one
    (P : PresentedStrictAffinoidAlgebra K) (a : P) :
    HasBoundedPowers a ↔ ∀ x : BanachSpectrum P, x a ≤ 1 :=
  ⟨fun ha x => ha.spectrum_le_one x, hasBoundedPowers_of_spectrum_le_one P a⟩

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
