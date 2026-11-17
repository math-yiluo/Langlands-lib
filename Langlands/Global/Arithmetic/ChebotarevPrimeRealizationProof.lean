import Langlands.Global.Arithmetic.ChebotarevStatement
import Langlands.AnthropicFLT.Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Chebotarev prime realization from the ported Anthropic FLT theorem

The ported theorem `NumberField.exists_prime_isArithFrobAt_of_isGalois` gives, for a finite
Galois extension `L / K` of number fields, an automorphism `σ` and a finite set of rational
primes, a rational prime `p` outside the set and a maximal ideal `Q` of `𝓞 L` containing `p`
at which `σ` is an arithmetic Frobenius over `ℤ`. This file converts that conclusion into the
Library's `ChebotarevPrimeRealizationStatement`: a height-one prime of `𝓞 K` outside a finite
set, a height-one prime of `𝓞 L` lying over it and unramified over `𝓞 K`, and the relative
arithmetic Frobenius property of `RingOfIntegers.mapAlgHom σ`.
-/

noncomputable section

universe u v

namespace Langlands.Global

open NumberField IsDedekindDomain
open scoped Pointwise NumberField

namespace ChebotarevRealization

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]

/-- A maximal ideal of `𝓞 L` containing a rational prime `p` lies over `p ℤ`. -/
theorem liesOver_of_prime_mem (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] (hm : (p : 𝓞 L) ∈ Q) :
    Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  exact (Ideal.liesOver_span_iff Ideal.IsPrime.ne_top'
    (Nat.prime_iff_prime_int.mp hp)).mpr (by simpa using hm)

/-- A prime of `𝓞 L` above a rational prime not dividing the discriminant of `L` is
unramified over `𝓞 K`. -/
theorem unramified_of_not_dvd_discr (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (hm : (p : 𝓞 L) ∈ Q)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr L) : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  have : Algebra.IsUnramifiedAt ℤ Q :=
    (NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L)
      (Nat.prime_iff_prime_int.mp hp)).mp hd Q inferInstance (by simpa using hm)
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q

/-- A height-one prime of `𝓞 K` over `p ℤ` is outside `S` once `p` avoids the absolute norms
of the contractions to `ℤ` of the members of `S`. -/
theorem outside_finite_set (S : Finset (HeightOneSpectrum (𝓞 K)))
    (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (havoid : p ∉ S.image (fun w => (w.asIdeal.under ℤ).absNorm)) : v ∉ S := by
  classical
  intro hv
  apply havoid
  have hc : (v.asIdeal.under ℤ).absNorm = p := by
    rw [← v.asIdeal.over_def (Ideal.span {(p : ℤ)}), Ideal.absNorm_span_natCast]
    simp
  exact hc ▸ Finset.mem_image_of_mem (fun w => (w.asIdeal.under ℤ).absNorm) hv

/-- If `σ ∈ Gal(L/K)` is an arithmetic Frobenius over `ℤ` at a maximal ideal `Q` above `p`,
the residue field of `𝓞 K` at `Q ∩ 𝓞 K` has `p` elements. -/
theorem base_card_eq_prime (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : L ≃ₐ[K] L) (hf : IsArithFrobAt ℤ σ Q) :
    Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = p := by
  classical
  have hZ : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [← Q.over_def (Ideal.span {(p : ℤ)}), Int.card_ideal_quot]
  let P := Q.under (𝓞 K)
  have hpow : ∀ y : 𝓞 K ⧸ P, y ^ p = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := hf (algebraMap (𝓞 K) (𝓞 L) x)
    have hfix : (MulSemiringAction.toAlgHom ℤ (𝓞 L) σ)
        (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap (𝓞 K) (𝓞 L) x := by
      apply RingOfIntegers.ext
      change σ (algebraMap K L (x : K)) = algebraMap K L (x : K)
      exact σ.commutes (x : K)
    rw [hZ, hfix, ← map_pow, ← map_sub] at hx
    rw [← map_pow, eq_comm, Ideal.Quotient.eq]
    exact hx
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hle : Nat.card (𝓞 K ⧸ P) ≤ p := by
    rw [Nat.card_eq_fintype_card]
    exact P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.P2mCycloSplit.card_le_of_forall_pow_eq
      hp.one_lt hpow
  have hZP : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    dsimp [P]
    rw [Ideal.under_under]
    exact hZ
  have hge : p ≤ Nat.card (𝓞 K ⧸ P) := by
    rw [← hZP]
    exact Nat.card_le_card_of_injective
      (algebraMap (ℤ ⧸ P.under ℤ) (𝓞 K ⧸ P)) Ideal.algebraMap_quotient_injective
  exact Nat.le_antisymm hle hge

/-- An arithmetic Frobenius over `ℤ` at a maximal ideal above `p` is an arithmetic Frobenius
of `RingOfIntegers.mapAlgHom σ` relative to `𝓞 K`. -/
theorem relative_frobenius (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : L ≃ₐ[K] L) (hf : IsArithFrobAt ℤ σ Q) :
    (RingOfIntegers.mapAlgHom σ).IsArithFrobAt Q := by
  have hc := base_card_eq_prime p hp Q σ hf
  have hZ : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [← Q.over_def (Ideal.span {(p : ℤ)}), Int.card_ideal_quot]
  intro x
  have hx := hf x
  rw [hZ] at hx
  rw [hc]
  exact hx

end ChebotarevRealization

open ChebotarevRealization in
/-- **Chebotarev's theorem, existence form.** Every automorphism of a finite Galois extension of
number fields is the arithmetic Frobenius at a prime that is unramified over the base and lies
above a base prime outside any given finite set. -/
theorem chebotarevPrimeRealizationStatement : ChebotarevPrimeRealizationStatement.{u, v} := by
  classical
  intro K _ _ L _ _ _ _ σ S
  let T := S.image (fun w => (w.asIdeal.under ℤ).absNorm) ∪
    (NumberField.discr L).natAbs.primeFactors
  obtain ⟨p, hp, hpT, Q, hQ, hpQ, hf⟩ :=
    NumberField.exists_prime_isArithFrobAt_of_isGalois K L σ T
  haveI : Q.IsMaximal := hQ
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_prime_mem p hp Q hpQ
  have hQ0 : Q ≠ ⊥ := (Q.bot_lt_of_maximal (RingOfIntegers.not_isField L)).ne'
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, hQ0⟩
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, Ideal.IsIntegral.under_ne_bot (𝓞 K) hQ0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := inferInstanceAs (Q.LiesOver (Q.under (𝓞 K)))
  haveI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    inferInstanceAs ((Q.under (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}))
  have hpS : p ∉ S.image (fun x => (x.asIdeal.under ℤ).absNorm) := by
    intro h
    exact hpT (Finset.mem_union_left _ h)
  have hd : ¬ (p : ℤ) ∣ NumberField.discr L := by
    intro hd
    have hn : p ∣ (NumberField.discr L).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hd
    exact hpT (Finset.mem_union_right _
      (hp.mem_primeFactors hn (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L))))
  exact ⟨v, outside_finite_set S p hp v hpS, w, inferInstance,
    unramified_of_not_dvd_discr (K := K) p hp Q hpQ hd,
    relative_frobenius p hp Q σ hf⟩

end Langlands.Global
