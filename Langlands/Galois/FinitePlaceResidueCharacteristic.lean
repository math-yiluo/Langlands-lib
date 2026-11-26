import Langlands.Galois.CompatibleFamily
import Langlands.Global.FiniteAdeleSplit

/-! # Rational primes and residue characteristics at finite places -/

namespace Langlands.GaloisRepresentation

universe uK

open Langlands.Global
open scoped NumberField

/-- A nonzero prime of `𝓞 K` containing the rational prime `p` has residue
characteristic `p`. -/
theorem residueCharacteristic_eq_of_natCast_mem {K : Type*} [Field K] [NumberField K]
    {v : FinitePlace K} {p : ℕ} (hp : p.Prime) (h : (p : 𝓞 K) ∈ v.asIdeal) :
    residueCharacteristic v = p := by
  have hq : (residueCharacteristic v).Prime := CharP.prime_ringChar (𝓞 K ⧸ v.asIdeal)
  have h0 : ((p : ℕ) : 𝓞 K ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (ringChar.dvd h0)

/-- The finite places of `K` of a given nonzero residue characteristic form a
finite set: their prime ideals contain that rational integer. -/
theorem finite_setOf_residueCharacteristic_eq (K : Type uK) [Field K] [NumberField K]
    {p : ℕ} (hp : p ≠ 0) :
    {v : FinitePlace K | residueCharacteristic v = p}.Finite := by
  refine (Set.finite_coe_iff.mp (finite_natCast_mem_asIdeal K p hp)).subset ?_
  intro v hv
  change residueCharacteristic v = p at hv
  change (p : 𝓞 K) ∈ v.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hv]
  exact CharP.cast_eq_zero (𝓞 K ⧸ v.asIdeal) (residueCharacteristic v)

end Langlands.GaloisRepresentation
