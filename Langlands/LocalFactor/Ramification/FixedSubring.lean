/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean`,
`Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup.lean`,
`Theorems/Thm_FixedPoints_isDiscreteValuationRing_subring.lean`,
`P2M/Sol/S_FixedPoints_isDiscreteValuationRing_subring.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the three files are merged; names follow the Library (`Langlands.Ramification`,
`…fixedSubring…` for upstream's `FixedPoints.…subring…`); the helper that proved the theorem on
discrete valuation rings is the theorem's proof; upstream's in-file checks are not kept; no
options are set. The paired Markdown file lists the changes.
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IsGaloisGroup.Defs

/-!
# The fixed subring of a group acting on a local ring

For a monoid `M` acting on a ring `R` by ring automorphisms, Mathlib's `FixedPoints.subring R M`
is the subring of invariants. This file shows that it is a local ring when `R` is (with the
inclusion a local homomorphism and the maximal ideal the contraction of that of `R`), that a
group acting faithfully on a commutative ring is a Galois group of the ring over its invariants,
and that the invariants of a finite group acting on a discrete valuation ring form a discrete
valuation ring.
-/

namespace Langlands.Ramification

section Ring

variable {R : Type*} [Ring R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem mem_fixedSubring_iff {x : R} :
    x ∈ FixedPoints.subring R M ↔ ∀ m : M, m • x = x :=
  Iff.rfl

theorem smul_eq_self_of_mem_fixedSubring_of_mul_eq_one {a b : R}
    (ha : a ∈ FixedPoints.subring R M) (hab : a * b = 1) (hba : b * a = 1) (m : M) :
    m • b = b := by
  have key : a * (m • b) = 1 := by
    have h : m • (a * b) = m • (1 : R) := congrArg (m • ·) hab
    rwa [smul_mul', mem_fixedSubring_iff.mp ha m, smul_one] at h
  exact (left_inv_eq_right_inv hba key).symm

theorem mem_fixedSubring_of_mul_eq_one {a b : R} (ha : a ∈ FixedPoints.subring R M)
    (hab : a * b = 1) (hba : b * a = 1) : b ∈ FixedPoints.subring R M :=
  mem_fixedSubring_iff.mpr fun m => smul_eq_self_of_mem_fixedSubring_of_mul_eq_one ha hab hba m

/-- An invariant element is a unit of the invariants exactly when it is a unit of the ring. -/
theorem isUnit_fixedSubring_iff (a : FixedPoints.subring R M) :
    IsUnit a ↔ IsUnit (a : R) := by
  constructor
  · intro h
    simpa using h.map (FixedPoints.subring R M).subtype
  · intro h
    obtain ⟨b, hab, hba⟩ := isUnit_iff_exists.mp h
    refine isUnit_iff_exists.mpr
      ⟨⟨b, mem_fixedSubring_of_mul_eq_one a.2 hab hba⟩, Subtype.ext ?_, Subtype.ext ?_⟩
    · simpa using hab
    · simpa using hba

instance isLocalHom_fixedSubring_subtype :
    IsLocalHom (FixedPoints.subring R M).subtype :=
  ⟨fun a h => (isUnit_fixedSubring_iff a).mpr (by simpa using h)⟩

/-- The invariants of a local ring form a local ring. -/
instance isLocalRing_fixedSubring [IsLocalRing R] :
    IsLocalRing (FixedPoints.subring R M) :=
  ⟨fun {a b} hab => by
    have h : (a : R) + (b : R) = 1 := by
      have h1 : ((a + b : FixedPoints.subring R M) : R) = ((1 : FixedPoints.subring R M) : R) :=
        congrArg Subtype.val hab
      simpa using h1
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h' | h'
    · exact Or.inl ((isUnit_fixedSubring_iff a).mpr h')
    · exact Or.inr ((isUnit_fixedSubring_iff b).mpr h')⟩

end Ring

theorem isLocalRing_fixedSubring_of_finite {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] :
    IsLocalRing (FixedPoints.subring R G) :=
  isLocalRing_fixedSubring

section MaximalIdeal

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem mem_maximalIdeal_fixedSubring_iff {a : FixedPoints.subring R M} :
    a ∈ IsLocalRing.maximalIdeal (FixedPoints.subring R M) ↔
      (a : R) ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff]
  exact not_congr (isUnit_fixedSubring_iff a)

/-- The maximal ideal of the invariants is the contraction of the maximal ideal of `R`. -/
theorem maximalIdeal_fixedSubring_eq_comap :
    IsLocalRing.maximalIdeal (FixedPoints.subring R M) =
      Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R) := by
  ext a
  rw [Ideal.mem_comap, Subring.subtype_apply]
  exact mem_maximalIdeal_fixedSubring_iff

theorem isMaximal_comap_maximalIdeal_fixedSubring :
    (Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R)).IsMaximal := by
  rw [← maximalIdeal_fixedSubring_eq_comap (R := R) (M := M)]
  exact IsLocalRing.maximalIdeal.isMaximal _

end MaximalIdeal

section Degenerate

variable {R : Type*} [Ring R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem fixedSubring_eq_top_of_forall_smul_eq (h : ∀ (m : M) (x : R), m • x = x) :
    FixedPoints.subring R M = ⊤ :=
  (Subring.eq_top_iff' _).mpr fun x => mem_fixedSubring_iff.mpr fun m => h m x

theorem fixedSubring_eq_top_of_subsingleton [Subsingleton M] :
    FixedPoints.subring R M = ⊤ :=
  fixedSubring_eq_top_of_forall_smul_eq fun m x => by
    rw [Subsingleton.elim m 1, one_smul]

/-- The invariants of a trivial monoid are the whole ring. -/
def fixedSubringEquivOfSubsingleton [Subsingleton M] :
    FixedPoints.subring R M ≃+* R :=
  (RingEquiv.subringCongr (fixedSubring_eq_top_of_subsingleton (R := R) (M := M))).trans
    Subring.topEquiv

end Degenerate

section Galois

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
  [FaithfulSMul G S]

/-- A group acting faithfully on a commutative ring is a Galois group of the ring over its
invariants. -/
theorem isGaloisGroup_fixedSubring : IsGaloisGroup G (FixedPoints.subring S G) S where
  faithful := inferInstance
  commutes := ⟨fun g r s => by
    show g • ((r : S) * s) = (r : S) * (g • s); rw [smul_mul', r.2 g]⟩
  isInvariant := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩

end Galois

/-! ### The invariants of a finite group acting on a discrete valuation ring -/

section DiscreteValuationRing

open IsLocalRing IsDiscreteValuationRing

namespace FixedSubring

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Fintype H] [MulSemiringAction H R]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The norm `∏ h, h • x` of an element is invariant. -/
theorem prod_smul_mem_fixedSubring (x : R) : (∏ h : H, h • x) ∈ FixedPoints.subring R H := by
  intro g
  rw [Finset.smul_prod']
  simp_rw [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

theorem exists_mem_fixedSubring_addVal_pos :
    ∃ s ∈ FixedPoints.subring R H, s ≠ 0 ∧ 0 < addVal R s := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  refine ⟨∏ h : H, h • π, prod_smul_mem_fixedSubring π, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro h _ hzero
    exact hπ.ne_zero ((smul_eq_zero_iff_eq (α := H) h).mp hzero)
  · have h1 : addVal R π ≤ addVal R (∏ h : H, h • π) := by
      rw [addVal_le_iff_dvd]
      simpa using Finset.dvd_prod_of_mem (fun h : H => h • π) (Finset.mem_univ (1 : H))
    exact lt_of_lt_of_le (by rw [addVal_uniformizer hπ]; exact zero_lt_one) h1

end FixedSubring

namespace FixedSubring

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [MulSemiringAction H R]

omit [IsDiscreteValuationRing R] in
theorem mem_fixedSubring_of_mul_mem {t c : R} (ht : t ∈ FixedPoints.subring R H) (ht0 : t ≠ 0)
    (htc : t * c ∈ FixedPoints.subring R H) : c ∈ FixedPoints.subring R H := by
  intro h
  have h1 : t * (h • c) = t * c := by
    have := htc h
    rw [smul_mul', ht h] at this
    exact this
  exact mul_left_cancel₀ ht0 h1

theorem exists_addVal_eq_natCast {s : R} (hs : s ≠ 0) : ∃ n : ℕ, addVal R s = n := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (fun h => hs (addVal_eq_top_iff.mp h))
  exact ⟨n, hn.symm⟩

end FixedSubring

open FixedSubring in
/-- The invariants of a finite group acting on a discrete valuation ring form a discrete
valuation ring. An invariant element of least positive valuation is a uniformizer of the
invariants. -/
theorem isDiscreteValuationRing_fixedSubring
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] :
    IsDiscreteValuationRing (FixedPoints.subring R H) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H

  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ s ∈ FixedPoints.subring R H, addVal R s = n
  have hP : ∃ n, P n := by
    obtain ⟨s, hs, hs0, hpos⟩ := exists_mem_fixedSubring_addVal_pos (R := R) (H := H)
    obtain ⟨n, hn⟩ := exists_addVal_eq_natCast hs0
    refine ⟨n, ?_, s, hs, hn⟩
    rw [hn] at hpos
    exact_mod_cast hpos
  obtain ⟨m, ⟨hm0, t, ht, htv⟩, hmin⟩ : ∃ m, P m ∧ ∀ n, P n → m ≤ n :=
    ⟨Nat.find hP, Nat.find_spec hP, fun n hn => Nat.find_min' hP hn⟩
  have ht0 : t ≠ 0 := fun h => by
    rw [h, addVal_zero] at htv
    exact ENat.top_ne_natCast m htv

  have hge : ∀ s ∈ FixedPoints.subring R H, s ≠ 0 → ¬ IsUnit s → (m : ℕ∞) ≤ addVal R s := by
    intro s hs hs0 hsu
    obtain ⟨n, hn⟩ := exists_addVal_eq_natCast hs0
    rw [hn]
    have hn0 : 0 < n := by
      by_contra h0
      have : n = 0 := by omega
      subst this
      exact hsu (addVal_eq_zero_iff.mp (by exact_mod_cast hn))
    exact_mod_cast hmin n ⟨hn0, s, hs, hn⟩

  have key : ∀ s ∈ FixedPoints.subring R H, s ≠ 0 →
      ∃ q : ℕ, ∃ c ∈ FixedPoints.subring R H, IsUnit c ∧ s = t ^ q * c := by
    intro s hs hs0
    obtain ⟨v, hv⟩ := exists_addVal_eq_natCast hs0
    refine ⟨v / m, ?_⟩
    have hdvd : t ^ (v / m) ∣ s := by
      rw [← addVal_le_iff_dvd, addVal_pow, htv, hv, nsmul_eq_mul]
      exact_mod_cast Nat.div_mul_le_self v m
    obtain ⟨c, hc⟩ := hdvd
    have hcS : c ∈ FixedPoints.subring R H :=
      mem_fixedSubring_of_mul_mem ((FixedPoints.subring R H).pow_mem ht _) (pow_ne_zero _ ht0)
        (hc ▸ hs)
    have hc0 : c ≠ 0 := by rintro rfl; exact hs0 (by simpa using hc)
    refine ⟨c, hcS, ?_, hc⟩
    by_contra hcu
    have h1 := hge c hcS hc0 hcu
    obtain ⟨w, hw⟩ := exists_addVal_eq_natCast hc0
    have h2 : addVal R s = addVal R (t ^ (v / m)) + addVal R c := by rw [hc, addVal_mul]
    rw [addVal_pow, htv, hv, hw, nsmul_eq_mul] at h2
    rw [hw] at h1
    have h2' : v = (v / m) * m + w := by exact_mod_cast h2
    have h1' : m ≤ w := by exact_mod_cast h1
    have h3 := Nat.div_add_mod v m
    have hlt : v % m < m := Nat.mod_lt v hm0
    have h4 : (v / m) * m = m * (v / m) := mul_comm _ _
    omega

  let τ : FixedPoints.subring R H := ⟨t, ht⟩
  have hτu : ¬ IsUnit τ := fun h => by
    have h' : IsUnit t := (isUnit_fixedSubring_iff τ).mp h
    have h1 : addVal R t = 0 := addVal_eq_zero_iff.mpr h'
    rw [htv] at h1
    exact hm0.ne' (by exact_mod_cast h1)
  have hτirr : Irreducible τ := by
    refine ⟨hτu, fun a b hab => ?_⟩
    by_contra hnot
    simp only [not_or] at hnot
    obtain ⟨hau, hbu⟩ := hnot
    have hab' : t = (a : R) * b := congrArg Subtype.val hab
    have ha0 : (a : R) ≠ 0 := fun h => ht0 (by rw [hab', h, zero_mul])
    have hb0 : (b : R) ≠ 0 := fun h => ht0 (by rw [hab', h, mul_zero])
    have ha := hge a a.2 ha0 (fun h => hau ((isUnit_fixedSubring_iff a).mpr h))
    have hb := hge b b.2 hb0 (fun h => hbu ((isUnit_fixedSubring_iff b).mpr h))
    have hsum : addVal R t = addVal R a + addVal R b := by rw [← addVal_mul, hab']
    rw [htv] at hsum
    have h1 : (m : ℕ∞) + m ≤ m := (add_le_add ha hb).trans hsum.symm.le
    have hmm : m + m ≤ m := by exact_mod_cast h1
    omega
  refine ofHasUnitMulPowIrreducibleFactorization ⟨τ, hτirr, ?_⟩
  intro x hx
  obtain ⟨q, c, hcS, hcu, hxc⟩ := key x x.2 (fun h => hx (Subtype.ext h))
  refine ⟨q, ?_⟩
  have hcu' : IsUnit (⟨c, hcS⟩ : FixedPoints.subring R H) :=
    (isUnit_fixedSubring_iff _).mpr hcu
  exact ⟨hcu'.unit, Subtype.ext (by simp [τ, hxc])⟩

end DiscreteValuationRing

end Langlands.Ramification
