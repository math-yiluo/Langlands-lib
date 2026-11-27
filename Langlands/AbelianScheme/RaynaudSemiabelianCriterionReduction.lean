import Langlands.AbelianScheme.RaynaudSemiabelianCriterionStatement
import Langlands.AbelianScheme.UnipotentInertiaSemiabelianReductionStatement
import Langlands.AbelianScheme.AbelianInertiaQuasiUnipotentStatement
import Langlands.AbelianScheme.RationalTorsionMonodromy

/-! # Raynaud's criterion from the monodromy theorem and the Galois criterion

`RaynaudSemiabelianCriterionReductionStatement` says that the Galois criterion
(`UnipotentInertiaSemiabelianReductionStatement`) and the quasi-unipotence of inertia
(`AbelianInertiaQuasiUnipotentStatement`) imply Raynaud's criterion
(`RaynaudSemiabelianCriterionStatement`), at the same universe.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.LinearAlgebra.CongruentQuasiUnipotent

namespace Langlands.AbelianScheme

/-- The Galois criterion and the quasi-unipotence of inertia imply Raynaud's criterion. -/
def RaynaudSemiabelianCriterionReductionStatement : Prop :=
  UnipotentInertiaSemiabelianReductionStatement.{u} →
    AbelianInertiaQuasiUnipotentStatement.{u} → RaynaudSemiabelianCriterionStatement.{u}

/-- A natural number `n ≥ 3` has a prime-power divisor `ℓ ^ a ≥ 3`: an odd prime factor,
or `4` when `n` is a power of `2`. -/
theorem exists_prime_pow_dvd_three_le (n : ℕ) (hn : 3 ≤ n) :
    ∃ ℓ a : ℕ, ℓ.Prime ∧ ℓ ^ a ∣ n ∧ 3 ≤ ℓ ^ a := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ≠ 2
  · obtain ⟨p, hp, hpn, hp2⟩ := h
    refine ⟨p, 1, hp, by simpa using hpn, ?_⟩
    have := hp.two_le
    rw [pow_one]
    omega
  · push Not at h
    have hn0 : n ≠ 0 := by omega
    have hpow : n = 2 ^ n.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hn0 fun {d} hd hdn => h d hd hdn
    have hk : 2 ≤ n.primeFactorsList.length := by
      by_contra hk
      push Not at hk
      interval_cases hk' : n.primeFactorsList.length <;> omega
    refine ⟨2, 2, Nat.prime_two, ?_, by norm_num⟩
    rw [hpow]
    exact pow_dvd_pow 2 hk

/-- Proof of the reduction. Choose a prime power `ℓ ^ a ≥ 3` dividing `n`. Let `W` be a
Henselian discrete valuation ring with separably closed residue field and a local
homomorphism `V → W` under which the maximal ideal of `V` generates that of `W`, and let `L`
be a fraction field of `W` with a field map `K → L` compatible with `V → W`; these are the
test rings of the Galois criterion. An element `g` of the fundamental group of `Spec L` acts
on the integral `ℓ`-adic Tate module by an endomorphism congruent to the identity modulo
`ℓ ^ a`, because the `n`-torsion is rational, and some positive power of it is unipotent by
quasi-unipotence. The linear-algebra lemma `isNilpotent_sub_one_of_isNilpotent_pow_sub_one`
makes `g` itself unipotent, and the Galois criterion concludes. -/
theorem raynaudSemiabelianCriterionReduction :
    RaynaudSemiabelianCriterionReductionStatement.{u} := by
  intro hG hQ V K _ _ _ _ _ _ B N n hn3 hnV hB
  obtain ⟨ℓ, a, hℓ, ha, h3⟩ := exists_prime_pow_dvd_three_le n hn3
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hn0 : 0 < n := by omega
  have hnK : IsUnit (n : K) := by simpa using hnV.map (algebraMap V K)
  have hℓn : ℓ ∣ n := (dvd_pow_self ℓ (by rintro rfl; norm_num at h3)).trans ha
  have hℓV : IsUnit (ℓ : V) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hℓn) hnV
  refine hG V K B N ℓ hℓV ?_
  intro W _ _ _ _ _ _ _ _ L _ _ _ _ _ Ω _ _ s hu g
  have hℓW : IsUnit (ℓ : W) := by simpa using hℓV.map (algebraMap V W)
  obtain ⟨m, hm, hnil⟩ := hQ W L ((baseChange (Spec.algebraMap K L)).obj B) ℓ hℓW Ω s hu g
  have hσ := RationalTorsionMonodromy.monodromyMap_sub_one_valuesDivisible s
    (geometricFiberFinite s) torsionFiniteEtale ((baseChange (Spec.algebraMap K L)).obj B) n ℓ
    (RationalTorsionMonodromy.torsionPointsRational_baseChange B n hB hn0 hnK L s) hu a ha g
  have hnilZ := (RationalTorsionMonodromy.isNilpotent_rationalMonodromy_pow_sub_one_iff _ ℓ s
    (geometricFiberFinite s) torsionFiniteEtale hu g m).mp hnil
  refine (RationalTorsionMonodromy.isNilpotent_rationalMonodromy_sub_one_iff _ ℓ s
    (geometricFiberFinite s) torsionFiniteEtale hu g).mpr ?_
  exact isNilpotent_sub_one_of_isNilpotent_pow_sub_one ℓ
    (RationalTorsionMonodromy.integral_eq_zero_of_nsmul_eq_zero _ _ ℓ)
    (RationalTorsionMonodromy.integral_eq_zero_of_forall_dvd _ _ ℓ) h3 hσ hm hnilZ

end Langlands.AbelianScheme
