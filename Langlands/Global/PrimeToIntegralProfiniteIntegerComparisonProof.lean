import Langlands.Global.PrimeToIntegralProfiniteIntegerComparison
import Langlands.Global.ProfiniteIntegerCompletionComparisonProof
import Langlands.Global.ProfiniteIntegerPadicProjection
import Langlands.Global.IntegralFiniteAdelePadicProduct
import Mathlib.Data.Nat.Factorization.Basic

noncomputable section

namespace Langlands.Global

open NumberField

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

private theorem away_place_iff (m : ℕ) (v : FinitePlace ℚ) :
    (m : 𝓞 ℚ) ∉ v.asIdeal ↔ Nat.Coprime (Rat.HeightOneSpectrum.primesEquiv v).val m := by
  rw [(Rat.HeightOneSpectrum.primesEquiv v).property.coprime_iff_not_dvd]
  apply not_congr
  rw [show (Rat.HeightOneSpectrum.primesEquiv v).val =
    Rat.HeightOneSpectrum.natGenerator v from rfl,
    Rat.HeightOneSpectrum.natGenerator_dvd_iff]
  exact (show Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) (m : 𝓞 ℚ) ∈
    v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) ↔ (m : 𝓞 ℚ) ∈ v.asIdeal from
      Ideal.apply_mem_of_equiv_iff).symm.trans (by simp)

private abbrev AwayPrime (m : ℕ) := {p : Nat.Primes // Nat.Coprime p.val m}

private def awayPlaceEquiv (m : ℕ) : PrimeToFinitePlace m ≃ AwayPrime m :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).subtypeEquiv (away_place_iff m)

private def awayIntegralProductEquiv (m : ℕ) :
    (∀ v : PrimeToFinitePlace m, v.val.adicCompletionIntegers ℚ) ≃+*
      primeToIntegralFiniteAdeles m where
  toFun x := ⟨RestrictedProduct.structureMap _ _ Filter.cofinite x, fun v => (x v).property⟩
  invFun a v := ⟨a.val v, a.property v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem continuous_awayIntegralProductEquiv (m : ℕ) :
    Continuous (awayIntegralProductEquiv m) := by
  apply continuous_induced_rng.mpr
  exact RestrictedProduct.isEmbedding_structureMap.continuous

private def awayPadicIntegralEquiv (m : ℕ) :
    (∀ p : AwayPrime m, PadicInt p.val.val) ≃+* primeToIntegralFiniteAdeles m :=
  ((RingEquiv.piCongrLeft (fun p : AwayPrime m => PadicInt p.val.val)
    (awayPlaceEquiv m)).symm.trans
      (RingEquiv.piCongrRight fun v =>
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v.val).symm.toRingEquiv)).trans
    (awayIntegralProductEquiv m)

private theorem continuous_awayPadicIntegralEquiv (m : ℕ) :
    Continuous (awayPadicIntegralEquiv m) := by
  apply (continuous_awayIntegralProductEquiv m).comp
  apply continuous_pi
  intro v
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v.val).symm.continuous.comp
    (continuous_apply (awayPlaceEquiv m v))

private def awayPadicProduct (m : ℕ) :
    PrimeToProfiniteIntegerRing m →+* (∀ p : AwayPrime m, PadicInt p.val.val) :=
  RingHom.pi fun p => PrimeToProfiniteIntegerRing.toPadic p.val.val m p.property

private theorem awayPadicProduct_injective (m : ℕ) :
    Function.Injective (awayPadicProduct m) := by
  intro x y hxy
  ext n
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (PrimeToProfiniteIntegerRing.reduction n x)
  obtain ⟨w, hw⟩ := ZMod.intCast_surjective (PrimeToProfiniteIntegerRing.reduction n y)
  change PrimeToProfiniteIntegerRing.reduction n x = PrimeToProfiniteIntegerRing.reduction n y
  rw [← hz, ← hw, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd]
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  let : Fact p.Prime := ⟨hp⟩
  by_cases hk : k = 0
  · simp [hk]
  have hpm : Nat.Coprime p m := n.property.of_dvd_left
    (dvd_trans (dvd_pow_self p hk) hpk)
  let q : AwayPrime m := ⟨⟨p, hp⟩, hpm⟩
  have he := congrArg (PadicInt.toZModPow k) (congrFun hxy q)
  have hred (a : PrimeToProfiniteIntegerRing m) (t : ℤ)
      (ht : (t : ZMod (n.val : ℕ)) = PrimeToProfiniteIntegerRing.reduction n a) :
      PadicInt.toZModPow k (PrimeToProfiniteIntegerRing.toPadic p m hpm a) =
        (t : ZMod (p ^ k)) := by
    rw [PrimeToProfiniteIntegerRing.toZModPow_toPadic,
      ← ResidueLimit.compatible a (PrimeToProfiniteIntegerRing.primePowerModulus p m hpm k) n hpk,
      ← ht]
    exact ResidueLimit.transition_intCast hpk t
  change PadicInt.toZModPow k (PrimeToProfiniteIntegerRing.toPadic p m hpm x) =
    PadicInt.toZModPow k (PrimeToProfiniteIntegerRing.toPadic p m hpm y) at he
  rw [hred x z hz, hred y w hw, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd] at he
  exact he

private def awayComparison (m : ℕ) :
    PrimeToProfiniteIntegerRing m →+* primeToIntegralFiniteAdeles m :=
  (awayPadicIntegralEquiv m).toRingHom.comp (awayPadicProduct m)

private theorem continuous_awayComparison (m : ℕ) : Continuous (awayComparison m) :=
  (continuous_awayPadicIntegralEquiv m).comp
    (continuous_pi fun p => PrimeToProfiniteIntegerRing.continuous_toPadic p.val.val m p.property)

private theorem awayComparison_integer (m : ℕ) (z : ℤ) :
    (awayComparison m (PrimeToProfiniteIntegerRing.intCastHom m z) : PrimeToFiniteAdeles m) =
      algebraMap ℚ (PrimeToFiniteAdeles m) (z : ℚ) := by
  change ((awayComparison m) (z : PrimeToProfiniteIntegerRing m) : PrimeToFiniteAdeles m) = _
  simp

private theorem integralRestriction_surjective (m : ℕ) :
    Function.Surjective (primeToIntegralRestriction m) := by
  classical
  intro a
  let x : ∀ v : FinitePlace ℚ, v.adicCompletionIntegers ℚ := fun v =>
    if h : (m : 𝓞 ℚ) ∉ v.asIdeal then ⟨a.val ⟨v, h⟩, a.property ⟨v, h⟩⟩ else 0
  refine ⟨integralFiniteAdelesProductEquiv ℚ x, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext v
  change (x v.val).val = a.val v
  simp [x, v.property]

/-- Every supplied normalized continuous full comparison descends to the integral
away comparison, for every natural modulus, with exactly that full witness. -/
theorem primeToIntegralProfiniteIntegerAdeleComparisons :
    PrimeToIntegralProfiniteIntegerAdeleComparisons := by
  intro eFull heFull _ hFull m
  have hcompat : awayComparison m ∘ PrimeToProfiniteIntegerRing.restrict m =
      primeToIntegralRestriction m ∘ eFull := by
    apply residue_integer_dense.equalizer
      ((continuous_awayComparison m).comp (PrimeToProfiniteIntegerRing.continuous_restrict m))
      ((continuous_primeToIntegralRestriction m).comp heFull)
    funext z
    apply Subtype.ext
    change (awayComparison m ((PrimeToProfiniteIntegerRing.restrict m)
      (ProfiniteIntegerRing.intCastHom z)) : PrimeToFiniteAdeles m) =
        primeToFiniteRestriction m (eFull (ProfiniteIntegerRing.intCastHom z))
    rw [show PrimeToProfiniteIntegerRing.restrict m (ProfiniteIntegerRing.intCastHom z) =
      PrimeToProfiniteIntegerRing.intCastHom m z from map_intCast _ z,
      awayComparison_integer, hFull, primeToFiniteRestriction_algebraMap]
  have hsurj : Function.Surjective (awayComparison m) := by
    intro a
    obtain ⟨b, hb⟩ := integralRestriction_surjective m a
    refine ⟨PrimeToProfiniteIntegerRing.restrict m (eFull.symm b), ?_⟩
    simpa using (congrFun hcompat (eFull.symm b)).trans (by simpa using hb)
  let e := RingEquiv.ofBijective (awayComparison m)
    ⟨(awayPadicIntegralEquiv m).injective.comp (awayPadicProduct_injective m), hsurj⟩
  have he : Continuous e := continuous_awayComparison m
  exact ⟨e, he, he.continuous_symm_of_equiv_compact_to_t2,
    awayComparison_integer m, fun a => congrFun hcompat a⟩

end Langlands.Global
