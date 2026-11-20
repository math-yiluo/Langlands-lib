import Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof

/-! # Finite Chebotarev realization at degree-one primes -/

noncomputable section

universe u v

namespace Langlands.Global

open NumberField IsDedekindDomain ChebotarevRealization
open scoped NumberField

/-- Degree-one refinement of the finite prime realization theorem. -/
def ChebotarevDegreeOneStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    ∀ (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K))),
      ∃ p : HeightOneSpectrum (𝓞 K), p ∉ S ∧ p.asIdeal.absNorm.Prime ∧
        ∃ q : HeightOneSpectrum (𝓞 L),
          q.asIdeal.LiesOver p.asIdeal ∧
          Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal ∧
          (RingOfIntegers.mapAlgHom σ).IsArithFrobAt q.asIdeal

/-- The arithmetic Frobenius in the prime realization may be taken above a
base prime whose residue field has prime cardinality. -/
theorem chebotarevDegreeOne : ChebotarevDegreeOneStatement.{u, v} := by
  classical
  intro K _ _ L _ _ _ _ σ S
  let T := S.image (fun w => (w.asIdeal.under ℤ).absNorm) ∪
    (NumberField.discr L).natAbs.primeFactors
  obtain ⟨p, hp, hpT, Q, hQ, hpQ, hf⟩ :=
    NumberField.exists_prime_isArithFrobAt_of_isGalois K L σ T
  let : Q.IsMaximal := hQ
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_prime_mem p hp Q hpQ
  have hQ0 : Q ≠ ⊥ := (Q.bot_lt_of_maximal (RingOfIntegers.not_isField L)).ne'
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, hQ0⟩
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, Ideal.IsIntegral.under_ne_bot (𝓞 K) hQ0⟩
  have : w.asIdeal.LiesOver v.asIdeal := inferInstanceAs (Q.LiesOver (Q.under (𝓞 K)))
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    inferInstanceAs ((Q.under (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}))
  have hvcard : v.asIdeal.absNorm = p := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact base_card_eq_prime p hp Q σ hf
  have hd : ¬ (p : ℤ) ∣ NumberField.discr L := by
    intro h
    have hn : p ∣ (NumberField.discr L).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr h
    exact hpT (Finset.mem_union_right _
      (hp.mem_primeFactors hn (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L))))
  exact ⟨v, outside_finite_set S p hp v (fun h => hpT (Finset.mem_union_left _ h)),
    hvcard.symm ▸ hp, w, inferInstance, unramified_of_not_dvd_discr (K := K) p hp Q hpQ hd,
    relative_frobenius p hp Q σ hf⟩

end Langlands.Global
