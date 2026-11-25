/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-! # Affine localization near an arbitrary closed subset

Source: Stacks Project, Tag 096V, Lemma `lemma-localization`, with `f = 1`, and Tag 092B
(blueprint: lem-weil-pbc-affine-closed-specialization-localization).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Localization at the elements invertible modulo `I` is weakly etale and identifies its
spectrum with the points specializing to `V(I)`. Every source point specializes to a point
above `V(I)`. Source: Stacks Project, Tags 096V and 092B
(blueprint: lem-weil-pbc-affine-closed-specialization-localization).

Proof:
1. The quotient-unit condition defines a multiplicative set. Apply
   `lem-weil-pbc-localization-ring-weakly-etale` and the affine equivalence in
   `definition-ind-etale-pro-etale-weakly` to obtain weak etaleness of the spectrum morphism.
2. `lem-weil-pbc-localization-spectrum-embedding` embeds the localization spectrum with
   image the primes disjoint from `S`.
3. If `p ≤ q` and `I ≤ q`, a member `s` of `S` cannot lie in `p`: lift an inverse of `s`
   modulo `I`; then `s * t - 1 ∈ I` would force `1 ∈ q`.
4. Conversely, if `p` avoids `S`, the ideal `p + I` is proper, since an equality
   `1 = a + i` with `a ∈ p` and `i ∈ I` makes `a` invertible modulo `I`. Use
   `lem-weil-pbc-proper-ideal-contained-in-maximal` to put `p + I` inside a maximal,
   hence prime, ideal `q`. This identifies the image; taking `p = q` includes `V(I)`.
5. Given a source point, choose such a `q` and lift it to the source using the image
   description. By `lem-weil-pbc-spec-localization-away-basic-open`, test specialization
   on basic opens. The denominator of a fraction is a unit, so its basic open equals
   that of its numerator. The inclusion `p ≤ q` gives the required specialization.
No finite-generation assumption on `I` is used. -/
theorem affineClosedSpecializationLocalization (A : Type u) [CommRing A] (I : Ideal A)
    (S : Submonoid A) (hS : ∀ a : A, a ∈ S ↔ IsUnit (Ideal.Quotient.mk I a)) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization S)))) ∧
    Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap A (Localization S))) ∧
    Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) =
      {p : PrimeSpectrum A | ∃ q : PrimeSpectrum A, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal} ∧
    {q : PrimeSpectrum A | I ≤ q.asIdeal} ⊆
      Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) ∧
    ∀ x : PrimeSpectrum (Localization S), ∃ y : PrimeSpectrum (Localization S),
      Specializes x y ∧ I ≤ (PrimeSpectrum.comap (algebraMap A (Localization S)) y).asIdeal := by
  have hweak : Algebra.WeaklyEtale A (Localization S) :=
    Algebra.WeaklyEtale.of_isLocalization A S (Localization S)
  have hweakSpec : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization S)))) :=
    (weaklyEtale_SpecMap_algebraMap_iff (R := A) (S := Localization S)).2 hweak
  have hemb : Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap A (Localization S))) :=
    PrimeSpectrum.localization_comap_isEmbedding (Localization S) S
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) =
      {p : PrimeSpectrum A | Disjoint (S : Set A) p.asIdeal} :=
    PrimeSpectrum.localization_comap_range (Localization S) S
  have hdisj_of_specializes {p q : PrimeSpectrum A}
      (hpq : p.asIdeal ≤ q.asIdeal) (hqI : I ≤ q.asIdeal) :
      Disjoint (S : Set A) p.asIdeal := by
    refine Set.disjoint_left.mpr ?_
    intro a haS hap
    obtain ⟨bbar, hab⟩ := (isUnit_iff_exists_inv.mp ((hS a).mp haS))
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bbar
    have hmk : Ideal.Quotient.mk I (a * b) = 1 := by
      simpa using hab
    have habI : a * b - 1 ∈ I :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem (a * b)).mp hmk
    have haq : a ∈ q.asIdeal := hpq hap
    have habq : a * b ∈ q.asIdeal := q.asIdeal.mul_mem_right b haq
    have hsubq : a * b - 1 ∈ q.asIdeal := hqI habI
    have h1q : (1 : A) ∈ q.asIdeal := by
      simpa using sub_mem habq hsubq
    exact q.isPrime.ne_top (q.asIdeal.eq_top_iff_one.mpr h1q)
  have hproper_of_disj {p : PrimeSpectrum A}
      (hp : Disjoint (S : Set A) p.asIdeal) : p.asIdeal ⊔ I ≠ ⊤ := by
    intro htop
    have hone : (1 : A) ∈ p.asIdeal ⊔ I := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, i, hi, hai⟩ := Submodule.mem_sup.mp hone
    have haiI : a - 1 ∈ I := by
      rw [show a - 1 = -i by rw [← hai]; ring]
      exact I.neg_mem hi
    have hmk : Ideal.Quotient.mk I a = 1 :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem a).mpr haiI
    have haS : a ∈ S := (hS a).mpr (by rw [hmk]; exact isUnit_one)
    exact Set.disjoint_left.mp hp haS ha
  have hrange_eq : Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) =
      {p : PrimeSpectrum A | ∃ q : PrimeSpectrum A, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal} := by
    rw [hrange]
    ext p
    constructor
    · intro hp
      obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal (p.asIdeal ⊔ I)
        (hproper_of_disj hp)
      refine ⟨⟨m, hm.isPrime⟩, ?_, ?_⟩
      · exact le_trans le_sup_right hpm
      · exact le_trans le_sup_left hpm
    · rintro ⟨q, hqI, hpq⟩
      exact hdisj_of_specializes hpq hqI
  refine ⟨hweakSpec, hemb, hrange_eq, ?_, ?_⟩
  · intro q hqI
    rw [hrange_eq]
    exact ⟨q, hqI, le_rfl⟩
  · intro x
    have hxrange : PrimeSpectrum.comap (algebraMap A (Localization S)) x ∈
        Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) := ⟨x, rfl⟩
    rw [hrange_eq] at hxrange
    obtain ⟨q, hqI, hxq⟩ := hxrange
    have hqrange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) := by
      rw [hrange_eq]
      exact ⟨q, hqI, le_rfl⟩
    obtain ⟨y, hy⟩ := hqrange
    rw [← hy] at hxq
    refine ⟨y, ?_, ?_⟩
    · apply (PrimeSpectrum.le_iff_specializes x y).mp
      apply (IsLocalization.under_le_under_iff S (Localization S)).mp
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.under_def] using hxq
    · simpa [hy] using hqI

end AlgebraicGeometry
