import Langlands.Global.ProfiniteIntegerPadicProductComparison
import Langlands.Global.ProfiniteIntegerPadicProjection
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

namespace Langlands.Global

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- A residue modulo `n` is determined by its reductions modulo the prime powers dividing `n`. -/
private theorem intCast_eq_of_primePow {n : ℕ} {z z' : ℤ}
    (h : ∀ (p : Nat.Primes) (k : ℕ), (p : ℕ) ^ k ∣ n →
      (z : ZMod ((p : ℕ) ^ k)) = (z' : ZMod ((p : ℕ) ^ k))) :
    (z : ZMod n) = (z' : ZMod n) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd]
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr fun p k hp hpk => ?_
  have hz := h ⟨p, hp⟩ k hpk
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd] at hz
  exact hz

/-- Chinese remainder theorem: prime-power coordinates of a p-adic family are
simultaneously realized by one integer modulo each positive modulus. -/
private theorem exists_intCast_eq_toZModPow (y : (p : Nat.Primes) → PadicInt (p : ℕ))
    (n : ℕ+) : ∃ z : ℤ, ∀ (p : Nat.Primes) (k : ℕ), (p : ℕ) ^ k ∣ (n : ℕ) →
      (z : ZMod ((p : ℕ) ^ k)) = PadicInt.toZModPow k (y p) := by
  classical
  let v : Nat.Primes → ℕ := fun p => (n : ℕ).factorization p
  let s : Nat.Primes → ℕ := fun p => (p : ℕ) ^ v p
  let a : Nat.Primes → ℕ := fun p => (PadicInt.toZModPow (v p) (y p)).val
  let t : Finset Nat.Primes :=
    (n : ℕ).primeFactors.preimage Subtype.val Subtype.val_injective.injOn
  have hs : ∀ p ∈ t, s p ≠ 0 := fun p _ => pow_ne_zero _ p.property.ne_zero
  have pp : Set.Pairwise (t : Set Nat.Primes) (Function.onFun Nat.Coprime s) := by
    intro p _ q _ hpq
    exact Nat.Coprime.pow _ _
      ((Nat.coprime_primes p.property q.property).mpr fun h => hpq (Subtype.ext h))
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset a s t hs pp
  refine ⟨c, fun p k hpk => ?_⟩
  have hkv : k ≤ v p := (p.property.pow_dvd_iff_le_factorization n.ne_zero).mp hpk
  have hmod : c ≡ a p [MOD s p] := by
    by_cases hp : p ∈ t
    · exact hc p hp
    · have hndvd : ¬ (p : ℕ) ∣ (n : ℕ) := fun hd =>
        hp (Finset.mem_preimage.mpr (Nat.mem_primeFactors.mpr ⟨p.property, hd, n.ne_zero⟩))
      have hv : v p = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd
      simp only [s, hv, pow_zero]
      exact Nat.modEq_one
  have : NeZero (s p) := ⟨pow_ne_zero _ p.property.ne_zero⟩
  have hcv : (c : ZMod (s p)) = PadicInt.toZModPow (v p) (y p) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod]
    exact ZMod.natCast_zmod_val _
  rw [← PadicInt.zmod_cast_comp_toZModPow k (v p) hkv, RingHom.comp_apply, ← hcv,
    ZMod.castHom_apply, Int.cast_natCast, ZMod.cast_natCast (pow_dvd_pow _ hkv)]

/-- The prime-power reductions of a residue family are the coordinates of its p-adic projections. -/
private theorem toZModPow_toPadic_eq_intCast {x : ProfiniteIntegerRing} {n : ℕ+} {z : ℤ}
    (hz : (z : ZMod (n : ℕ)) = ProfiniteIntegerRing.reduction n x)
    (p : Nat.Primes) (k : ℕ) (hpk : (p : ℕ) ^ k ∣ (n : ℕ)) :
    PadicInt.toZModPow k (ProfiniteIntegerRing.toPadic p x) = (z : ZMod ((p : ℕ) ^ k)) := by
  rw [ProfiniteIntegerRing.toZModPow_toPadic]
  rw [← ResidueLimit.compatible x (ProfiniteIntegerRing.primePowerModulus p k) n hpk, ← hz]
  exact ResidueLimit.transition_intCast hpk z

/-- The product of the canonical p-adic projections. -/
private def toPadicProduct : ProfiniteIntegerRing →+* ((p : Nat.Primes) → PadicInt (p : ℕ)) :=
  RingHom.pi fun p => ProfiniteIntegerRing.toPadic p

private theorem toPadicProduct_injective : Function.Injective toPadicProduct := by
  intro x x' hxx'
  ext n
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (ProfiniteIntegerRing.reduction n x)
  obtain ⟨z', hz'⟩ := ZMod.intCast_surjective (ProfiniteIntegerRing.reduction n x')
  change ProfiniteIntegerRing.reduction n x = ProfiniteIntegerRing.reduction n x'
  rw [← hz, ← hz']
  apply intCast_eq_of_primePow
  intro p k hpk
  rw [← toZModPow_toPadic_eq_intCast hz p k hpk, ← toZModPow_toPadic_eq_intCast hz' p k hpk]
  exact congrArg (PadicInt.toZModPow k) (congrFun hxx' p)

private theorem toPadicProduct_surjective : Function.Surjective toPadicProduct := by
  intro y
  choose z hz using exists_intCast_eq_toZModPow y
  refine ⟨⟨fun n => (z n : ZMod (n : ℕ)), ?_⟩, ?_⟩
  · intro i j h
    change ResidueLimit.transition h (z j : ZMod (j : ℕ)) = (z i : ZMod (i : ℕ))
    rw [ResidueLimit.transition_intCast]
    apply intCast_eq_of_primePow
    intro p k hpk
    rw [hz j p k (dvd_trans hpk h), hz i p k hpk]
  · funext p
    apply PadicInt.ext_of_toZModPow.mp
    intro k
    change PadicInt.toZModPow k (ProfiniteIntegerRing.toPadic p _) = _
    rw [toZModPow_toPadic_eq_intCast (n := ProfiniteIntegerRing.primePowerModulus p k)
      (z := z (ProfiniteIntegerRing.primePowerModulus p k)) rfl p k dvd_rfl]
    exact hz _ p k dvd_rfl

/-- The residue-limit ring is continuously ring-isomorphic to the product of the
p-adic integer rings, compatibly with the canonical integer maps. -/
theorem profiniteIntegerPadicProductComparison : ProfiniteIntegerPadicProductComparison := by
  let e := RingEquiv.ofBijective toPadicProduct
    ⟨toPadicProduct_injective, toPadicProduct_surjective⟩
  have he : Continuous e :=
    continuous_pi fun p => ProfiniteIntegerRing.continuous_toPadic p
  refine ⟨e, he, he.continuous_symm_of_equiv_compact_to_t2, ?_⟩
  intro z p
  exact ProfiniteIntegerRing.toPadic_intCast p z

end Langlands.Global
