import Langlands.GaloisCohomology.Global.PoitouTate.LocalDuality
import Langlands.GaloisCohomology.Global.RealPlaces.HighDegree
import Langlands.GaloisCohomology.Global.Units.HighDegree
import Langlands.GaloisCohomology.CompactSupport.BaseCase

/-!
# The hypotheses of the abstract Poitou–Tate theorems for `G_S`

The abstract nine-term sequence with Tate's `Ĥ⁰` (`TatePoitouTateHypotheses` of
`Langlands.GaloisCohomology.CompactSupport.TateModified.NineTerm`) needs, for a profinite group with
two families of local groups, a dualizing module `D ≅ ℤ/N`, a trace and local invariants:
the duality with compact support for finite modules killed by `N`, finiteness in degrees `≤ 2`,
the compatibility of the trace with the local invariants, injectivity of `H⁰` into the first family,
and the surjectivity of the local pairings.

For `G_S` with the localizations at the places of `S` and at the real places, `D = μ_N`, the trace
`trace` and the invariants `invariantAt`, `realInvariantAt`, this file proves all of these except one,
which enters as the hypothesis of `tatePoitouTateHypotheses_of`: the duality with compact support
itself. The others come from:

* `μ_N(K_S) ≅ ℤ/N` because `K_S` contains the `N`-th roots of unity (`nonempty_addEquiv_dualizingModule`);
* finiteness: `finite_cohomology` of `Langlands.GaloisCohomology.Global.RealPlaces.HighDegree`, with
  the places above `#M` inside those above `N` (`natCast_mem_of_natCard_mem`);
* the trace: `trace_localToCompact`;
* `H⁰`: `S` is not empty when `N ≠ 1` (`nonempty_of_natCast_mem`), and restriction in degree `0` is
  injective;
* the real places: `surjective_realPairing_zero`, `exists_realPairing_two`;
* the finite places: `surjective_localPairing` (local Tate duality, `localTateDualityStatement`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Places

variable {K : Type u} [Field K] [NumberField K]

/-- If a natural number lies in a prime ideal of a ring, so does one of its prime factors. -/
theorem exists_prime_dvd_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {n : ℕ}
    (hn : n ≠ 0) (h : (n : R) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : R) ∈ P := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one P).2 h) (Ideal.IsPrime.ne_top ‹_›)
  | prime p hp => exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b ha hb =>
    rw [Nat.cast_mul] at h
    rcases Ideal.IsPrime.mem_or_mem ‹_› h with h' | h'
    · obtain ⟨p, hp, hpa, hpP⟩ := ha (left_ne_zero_of_mul hn) h'
      exact ⟨p, hp, hpa.mul_right b, hpP⟩
    · obtain ⟨p, hp, hpb, hpP⟩ := hb (right_ne_zero_of_mul hn) h'
      exact ⟨p, hp, hpb.mul_left a, hpP⟩

omit [NumberField K] in
/-- The places above the order of a finite group killed by `N` lie above `N`. -/
theorem natCast_mem_of_natCard_mem {A : Type*} [AddCommGroup A] [Finite A] {N : ℕ}
    (hA : ∀ a : A, N • a = 0) (v : HeightOneSpectrum (𝓞 K))
    (hv : ((Nat.card A : ℕ) : 𝓞 K) ∈ v.asIdeal) : ((N : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  obtain ⟨p, hp, hpA, hpv⟩ := exists_prime_dvd_natCast_mem v.asIdeal Nat.card_pos.ne' hv
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' (G := A) p hpA
  obtain ⟨k, rfl⟩ : p ∣ N := ha ▸ addOrderOf_dvd_of_nsmul_eq_zero (hA a)
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hpv

/-- If `S` contains the places above `N ≠ 1`, it is not empty. -/
theorem nonempty_of_natCast_mem {S : Set (HeightOneSpectrum (𝓞 K))} {N : ℕ} (hN : N ≠ 1)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) : Nonempty S := by
  obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd hN
  obtain ⟨v, hv⟩ := exists_natCast_mem_asIdeal (K := K) hp
  refine ⟨⟨v, hS v ?_⟩⟩
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

end Places

section Roots

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {N : ℕ} [NeZero N]

/-- `μ_N(K_S)` is cyclic of order `N` when `S` contains the places above `N`. -/
theorem nonempty_addEquiv_dualizingModule
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Nonempty (dualizingModule K Ω S N ≃+ ZMod N) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  have : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
  have hmem : ζ ∈ maximalUnramifiedOutside K Ω S :=
    mem_maximalUnramifiedOutside_of_pow_eq_one S (NeZero.ne N) (fun v hv h => hv (hS v h))
      hζ.pow_eq_one
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : maximalUnramifiedOutside K Ω S) N :=
    IsPrimitiveRoot.of_map_of_injective (f := (maximalUnramifiedOutside K Ω S).val) hζ
      (maximalUnramifiedOutside K Ω S).val.toRingHom.injective
  have hcard : Nat.card (rootsOfUnity N (maximalUnramifiedOutside K Ω S)) = N :=
    hζ'.card_rootsOfUnity
  have : IsAddCyclic (Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S))) :=
    isAddCyclic_additive_iff.2 inferInstance
  exact ⟨addEquivOfAddCyclicCardEq (G := Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S)))
    (G' := ZMod N) (by rw [Nat.card_zmod]; exact (Nat.card_congr Additive.ofMul.symm).trans hcard)⟩

end Roots

section Assembly

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (N : ℕ) [NeZero N]

omit [Finite S] in
/-- Restriction of `H⁰(G_S, M)` to the places of `S` is injective when `S` is not empty. -/
theorem injective_ptRes_zero [Nonempty S]
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] :
    Function.Injective fun (x : cohomology M 0) v => ptRes (localFamily ι S) M v 0 x := by
  obtain ⟨v⟩ := ‹Nonempty S›
  exact fun x y hxy => injective_map_zero (localizationHom ι S v) M (congrFun hxy v)

/-- **The hypotheses of the abstract nine-term sequence for `G_S`**, from the Tate-modified duality
with compact support for finite modules killed by `N` (`N ≠ 1`). -/
theorem tatePoitouTateHypotheses_of
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) (hN : N ≠ 1)
    (hdual : ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
      [Finite M], (∀ m : M, N • m = 0) → ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s →
        Function.Bijective (tateCompactDualityMap (localFamily ι S) (realFamily ι S)
          (dualizingModule K Ω S N) h (trace ι S N) M)) :
    letI : Fintype S := Fintype.ofFinite S
    TatePoitouTateHypotheses (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N)
      (trace ι S N) (fun v => invariantAt ι S N v) (fun w => realInvariantAt ι S N w.1) := by
  let _ : Fintype S := Fintype.ofFinite S
  have hD := nonempty_addEquiv_dualizingModule (Ω := Ω) hS
  have : Nonempty S := nonempty_of_natCast_mem hN hS
  exact
    { nonempty_addEquiv := hD
      duality := @fun M _ _ hM r s h hs => hdual M hM h hs
      finite_cohomology := fun M _ _ hM r _ =>
        finite_cohomology S M (fun v hv => hS v (natCast_mem_of_natCard_mem hM v hv)) r
      localToCompact_two := fun ξ => (trace_localToCompact ι S N ξ).trans (sumInvariants_apply ι S N ξ)
      injective_res_zero := fun M _ => injective_ptRes_zero ι S M
      surjective_localPairing_zero := fun M _ _ hM v => surjective_localPairing ι S N M hD hM v _
      surjective_localPairing_two := fun M _ _ hM v => surjective_localPairing ι S N M hD hM v _
      surjective_realPairing_zero := fun M _ _ hM w => surjective_realPairing_zero ι S N M hD hM w
      surjective_realPairing_two := fun M _ _ hM w χ hχ =>
        exists_realPairing_two ι S N M hD hM w χ hχ }

end Assembly

end

end Langlands.GaloisCohomology.PoitouTate
