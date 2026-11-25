/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Jacobson radical descends through an integral overring

Source: Stacks Project, Varieties Lemma 09N2 proof, paragraph beginning
“Moreover, `Spec(B') -> Spec(A)` is surjective” (blueprint:
lem-sc-integral-overring-jacobson-power).
-/

@[expose] public section

universe u v w

/--
(blueprint: lem-sc-integral-overring-jacobson-power)
Let `B` be a semilocal commutative ring, let `B'` be a semilocal commutative
ring integral over `B`, and let `A` be an intermediate commutative ring.
If `Spec(B') → Spec(A)` is surjective, then `A` is semilocal and
`J(A) = √(m_B A)`.  Every element of `A` lying in `J(B')` therefore has a
positive power in `m_B A`.  This is the Jacobson-radical argument in
Stacks, Varieties Lemma 09N2, proof of `lemma-semi-local-dimension-one-conductor`.

Proof (following the blueprint node):
1. Injectivity and the scalar tower identify `B ⊆ A ⊆ B'`. Integrality of `B'`
   over `B` implies integrality of `A` over `B` and of `B'` over `A`
   (def-weil-pbc-integral-closure).
2. Spec-surjectivity lifts each maximal ideal of `A` to a prime of `B'`.
   Integrality makes that prime maximal
   (lem-weil-pbc-integral-prime-over-maximal-maximal), and contraction of a maximal
   ideal is maximal (lem-weil-pbc-integral-algebra-ideal-in-radical). Thus the
   maximal ideals of `A` are contractions of the finitely many maximal ideals of `B'`.
3. Integrality gives `m_B A ≤ J(A)`
   (lem-weil-pbc-integral-algebra-ideal-in-radical), hence `√(m_B A) ≤ J(A)`.
   A prime of `A` containing `m_B A` contracts to a prime containing the finite
   intersection of the maximal ideals of `B`. Their product lies in this
   intersection, so primality forces the contraction to contain one maximal ideal,
   hence to equal it. The original prime is then maximal
   (lem-weil-pbc-integral-prime-over-maximal-maximal). The intersection of these
   primes therefore contains `J(A)`, proving the reverse inclusion. If `B` has no
   maximal ideals, `m_B` and its extension are the unit ideals, and equality holds.
4. An element of `A` mapping into `J(B')` lies in every maximal ideal of `A`
   by step 2. Step 3 puts it in `√(m_B A)`, so a positive power lies in `m_B A`.
-/
theorem integral_overring_jacobson_power
    (B : Type u) (A : Type v) (B' : Type w)
    [CommRing B] [CommRing A] [CommRing B']
    [Algebra B A] [Algebra A B'] [Algebra B B']
    [IsScalarTower B A B']
    [Finite (MaximalSpectrum B)] [Finite (MaximalSpectrum B')]
    [Algebra.IsIntegral B B']
    [FaithfulSMul B A] [FaithfulSMul A B']
    (hspec : Function.Surjective (PrimeSpectrum.comap (algebraMap A B')))
    : Finite (MaximalSpectrum A) ∧
      Ideal.jacobson (⊥ : Ideal A) =
        (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))).radical ∧
      ∀ (x : A),
        algebraMap A B' x ∈ Ideal.jacobson (⊥ : Ideal B') →
          ∃ m : ℕ, 0 < m ∧
            x ^ m ∈ Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B)) := by
  classical
  have : Algebra.IsIntegral A B' := ⟨fun x ↦
    (Algebra.IsIntegral.isIntegral (R := B) x).tower_top⟩
  have : Algebra.IsIntegral B A := ⟨fun x ↦
    (isIntegral_algebraMap_iff (R := B) (A := A) (B := B')).mp
        (Algebra.IsIntegral.isIntegral (R := B) (algebraMap A B' x))⟩
  have lift (p : MaximalSpectrum A) :
      ∃ q : MaximalSpectrum B', Ideal.comap (algebraMap A B') q.asIdeal = p.asIdeal := by
    obtain ⟨q, hq⟩ := hspec ⟨p.asIdeal, p.isMaximal.isPrime⟩
    have heq : Ideal.comap (algebraMap A B') q.asIdeal = p.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hq
    have hm : q.asIdeal.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) q.asIdeal (by
        change (Ideal.comap (algebraMap A B') q.asIdeal).IsMaximal
        rw [heq]
        exact p.isMaximal)
    exact ⟨⟨q.asIdeal, hm⟩, heq⟩
  let f : MaximalSpectrum B' → MaximalSpectrum A := fun q ↦
    ⟨Ideal.comap (algebraMap A B') q.asIdeal,
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) q.asIdeal⟩
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨q, hq⟩ := lift p
    exact ⟨q, MaximalSpectrum.ext hq⟩
  have hfinite : Finite (MaximalSpectrum A) := Finite.of_surjective f hf
  have hmap : Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B)) ≤
      Ideal.jacobson (⊥ : Ideal A) := by
    change _ ≤ sInf {p : Ideal A | ⊥ ≤ p ∧ p.IsMaximal}
    apply le_sInf
    intro p hp
    have : p.IsMaximal := hp.2
    apply Ideal.map_le_iff_le_comap.mpr
    exact sInf_le ⟨bot_le, Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) p⟩
  have hrad : Ideal.jacobson (⊥ : Ideal A) =
      (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))).radical := by
    apply le_antisymm
    · rw [Ideal.radical_eq_sInf, le_sInf_iff]
      intro p hp
      have : p.IsPrime := hp.2
      let r := Ideal.comap (algebraMap B A) p
      have hr : r.IsPrime := Ideal.comap_isPrime _ _
      have hj : Ideal.jacobson (⊥ : Ideal B) ≤ r :=
        Ideal.map_le_iff_le_comap.mp hp.1
      let := Fintype.ofFinite (MaximalSpectrum B)
      have hi : (⨅ q : MaximalSpectrum B, q.asIdeal) ≤ r := by
        apply le_trans ?_ hj
        rw [Ideal.jacobson, le_sInf_iff]
        intro q hq
        exact iInf_le (fun q : MaximalSpectrum B ↦ q.asIdeal) ⟨q, hq.2⟩
      obtain ⟨q, _, hq⟩ := (hr.inf_le' (s := Finset.univ)
        (f := fun q : MaximalSpectrum B ↦ q.asIdeal)).mp
          (by rwa [Finset.inf_univ_eq_iInf])
      have hm : r.IsMaximal := (q.isMaximal.eq_of_le hr.ne_top hq) ▸ q.isMaximal
      have : p.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) p hm
      exact sInf_le ⟨bot_le, this⟩
    · exact (Ideal.isRadical_jacobson ⊥).radical_le_iff.mpr hmap
  refine ⟨hfinite, hrad, ?_⟩
  intro x hx
  have hxA : x ∈ Ideal.jacobson (⊥ : Ideal A) := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    intro p hp
    obtain ⟨q, hq⟩ := lift ⟨p, hp.2⟩
    have hxq : algebraMap A B' x ∈ q.asIdeal :=
      (show Ideal.jacobson (⊥ : Ideal B') ≤ q.asIdeal from
        sInf_le ⟨bot_le, q.isMaximal⟩) hx
    have hxc : x ∈ Ideal.comap (algebraMap A B') q.asIdeal := hxq
    simpa only [hq] using hxc
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp (hrad ▸ hxA)
  by_cases hpos : 0 < m
  · exact ⟨m, hpos, hm⟩
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hpos
    rw [hm0, pow_zero] at hm
    exact ⟨1, Nat.one_pos, by simpa using
      (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))).mul_mem_left x hm⟩
