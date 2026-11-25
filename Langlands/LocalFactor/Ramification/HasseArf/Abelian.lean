/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean`,
`Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the four files (two statements and their proofs) are one module; the FLT proof name
space `P2MW.<file>.HasseArfRed` is `Langlands.Ramification.HasseArf.Abelian`; statements are on the
Library's `Langlands.Ramification.lowerGroup`; names follow the Library; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.FixedSubringQuotient
import Langlands.LocalFactor.Ramification.HasseArf.Cyclic
import Langlands.LocalFactor.Ramification.Herbrand.LowerQuotient
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The Hasse–Arf theorem for an abelian group

The Hasse–Arf theorem for a finite abelian group acting faithfully on a discrete valuation ring
with perfect residue field and separable residue extension over the invariants: at every break
`i` of the lower filtration, `φ(i)` is an integer (`HasseArfChain`). It is reduced to cyclic
quotients: an element of `G_i` outside `G_{i+1}` survives in a cyclic quotient `G ⧸ H` in which,
by the compatibility of the upper numbering with quotients, `φ_G(i)` is a break of the upper
filtration, hence an integer by the cyclic case.
-/

namespace Langlands.Ramification

section

section
attribute [-simp] lowerGroup_subgroupOf lowerGroup_map_subtype

namespace HasseArf.Abelian

open IsLocalRing

section upper
variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]

theorem upperGroupRat_le_succ_of_lt {i : ℕ} {w : ℚ} (hw : herbrandPhiRat R G i < w) :
    upperGroupRat R G w ≤ lowerGroup R G (i + 1) := by
  apply (lowerGroup_antitone _ _)

  by_contra h
  push Not at h
  have h1 : (upperGroupRatIndex R G w : ℕ) ≤ i := Nat.lt_succ_iff.mp h
  have h2 := le_herbrandPhiRat_upperGroupRatIndex (R := R) (G := G) w
  have h3 : herbrandPhiRat R G (upperGroupRatIndex R G w : ℕ) ≤ herbrandPhiRat R G i :=
    herbrandPhiRat_monotone (by exact_mod_cast h1)
  exact absurd (h2.trans h3) (not_le.mpr hw)

theorem exists_jump_of_upper {v : ℚ} (hv : upperGroupRat R G v ≠ ⊥)
    (hw : ∀ w : ℚ, v < w → upperGroupRat R G w = ⊥) :
    ∃ c : ℕ, lowerGroup R G c ≠ lowerGroup R G (c + 1) ∧ herbrandPhiRat R G c = v := by
  refine ⟨upperGroupRatIndex R G v, ?_, ?_⟩
  ·
    intro h
    have e1 : upperGroupRat R G v = lowerGroup R G (upperGroupRatIndex R G v) := rfl
    have hlt : v < herbrandPhiRat R G ((upperGroupRatIndex R G v + 1 : ℕ) : ℚ) := by
      refine lt_of_le_of_lt (le_herbrandPhiRat_upperGroupRatIndex v) (herbrandPhiRat_strictMono ?_)
      exact_mod_cast Nat.lt_succ_self _
    have e2 := hw _ hlt
    rw [upperGroupRat_herbrandPhiRat_natCast] at e2
    exact hv (by rw [e1, h]; exact_mod_cast e2)
  ·
    rcases (le_herbrandPhiRat_upperGroupRatIndex (R := R) (G := G) v).lt_or_eq with hlt | heq
    · have e2 := hw _ hlt
      rw [upperGroupRat_herbrandPhiRat_natCast] at e2
      exact absurd e2 hv
    · exact heq.symm

theorem exists_herbrandPhiRat_eq_natCast (hHA : HasseArfChain (lowerGroup R G)) {c : ℕ}
    (hc : lowerGroup R G c ≠ lowerGroup R G (c + 1)) : ∃ m : ℕ, herbrandPhiRat R G c = m := by
  obtain ⟨k, hk⟩ := hHA c hc
  refine ⟨k, ?_⟩
  rw [herbrandPhiRat_natCast]
  have h0 : (lowerGroupCard R G 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (lowerGroupCard_pos (R := R) (G := G) 0).ne'
  rw [div_eq_iff h0]
  have : (∑ i ∈ Finset.Icc 1 c, (lowerGroupCard R G i : ℚ)) = ((∑ j ∈ Finset.Icc 1 c, Nat.card ↥(lowerGroup R G j) : ℕ) : ℚ) := by
    rw [Nat.cast_sum]; rfl
  rw [this, hk, Nat.cast_mul, mul_comm]
  rfl

theorem dvd_of_herbrandPhiRat_eq_natCast {c : ℕ} {m : ℕ} (h : herbrandPhiRat R G c = m) :
    Nat.card ↥(lowerGroup R G 0) ∣ ∑ j ∈ Finset.Icc 1 c, Nat.card ↥(lowerGroup R G j) := by
  refine ⟨m, ?_⟩
  have h0 : (lowerGroupCard R G 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (lowerGroupCard_pos (R := R) (G := G) 0).ne'
  rw [herbrandPhiRat_natCast, div_eq_iff h0] at h
  have e : ((∑ j ∈ Finset.Icc 1 c, Nat.card ↥(lowerGroup R G j) : ℕ) : ℚ) = ((Nat.card ↥(lowerGroup R G 0) * m : ℕ) : ℚ) := by
    rw [Nat.cast_sum, Nat.cast_mul, mul_comm]
    exact h
  exact_mod_cast e

end upper

section cyclicQuotient
variable {G : Type*} [Group G] [Finite G] [IsMulCommutative G]

open scoped IsMulCommutative in

theorem exists_normal_isCyclic_quotient (N : Subgroup G) (g : G) (hg : g ∉ N) :
    ∃ H : Subgroup G, N ≤ H ∧ g ∉ H ∧ IsCyclic (G ⧸ H) := by
  haveI : N.Normal := Subgroup.normal_of_isMulCommutative N
  have hne : (QuotientGroup.mk g : G ⧸ N) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ N) ℂ hne
  let ψ : G →* ℂˣ := φ.comp (QuotientGroup.mk' N)
  refine ⟨ψ.ker, fun n hn => ?_, fun h => hφ ?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    change φ (QuotientGroup.mk n) = 1
    rw [(QuotientGroup.eq_one_iff n).2 hn, map_one]
  · rwa [MonoidHom.mem_ker] at h
  · haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    haveI : IsCyclic ψ.range := isCyclic_subgroup_units ψ.range
    exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange ψ).symm.surjective

end cyclicQuotient

end HasseArf.Abelian

theorem hasseArfChain_lowerGroup_of_forall_isCyclic_quotient
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hcyc : ∀ (H : Subgroup G) [H.Normal], IsCyclic (G ⧸ H) →
      HasseArfChain
        (lowerGroup (FixedPoints.subring R H) (G ⧸ H))) :
    HasseArfChain (lowerGroup R G) := by
  classical
  intro i hi

  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp

  have hlt : lowerGroup R G (i + 1) < lowerGroup R G i :=
    lt_of_le_of_ne ((lowerGroup_antitone _ _) (Nat.le_succ i)) (Ne.symm hi)
  obtain ⟨g, hgi, hgi'⟩ := IsConcreteLE.exists_of_lt hlt

  obtain ⟨H, hNH, hgH, hcycH⟩ := HasseArf.Abelian.exists_normal_isCyclic_quotient (lowerGroup R G (i + 1)) g hgi'
  haveI hHn : H.Normal := Subgroup.normal_of_isMulCommutative H

  have hcompat : UpperGroupRatQuotientCompat R G (FixedPoints.subring R H) H :=
    upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq
      (fun n => map_lowerGroup_mk_eq_of_isSeparable_residueField (R := R) (G := G) (H := H) n)

  set v : ℚ := herbrandPhiRat R G i with hvdef
  have hv0 : 0 ≤ v := herbrandPhiRat_nonneg (by exact_mod_cast Nat.zero_le i)
  have hQv : upperGroupRat (FixedPoints.subring R H) (G ⧸ H) v ≠ ⊥ := by
    rw [← hcompat v hv0, upperGroupRat_herbrandPhiRat_natCast]
    intro h
    have : QuotientGroup.mk' H g ∈ (lowerGroup R G i).map (QuotientGroup.mk' H) := Subgroup.mem_map_of_mem _ hgi
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hgH this
  have hQw : ∀ w : ℚ, v < w → upperGroupRat (FixedPoints.subring R H) (G ⧸ H) w = ⊥ := by
    intro w hw
    rw [← hcompat w (hv0.trans hw.le), eq_bot_iff]
    refine (Subgroup.map_mono (HasseArf.Abelian.upperGroupRat_le_succ_of_lt hw)).trans ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hNH hx
  obtain ⟨c, hc, hφc⟩ := HasseArf.Abelian.exists_jump_of_upper hQv hQw

  obtain ⟨m, hm⟩ := HasseArf.Abelian.exists_herbrandPhiRat_eq_natCast (hcyc H hcycH) hc
  exact HasseArf.Abelian.dvd_of_herbrandPhiRat_eq_natCast (R := R) (G := G) (m := m) (by rw [← hvdef, ← hφc, hm])

end

end

section

section
attribute [-simp] lowerGroup_subgroupOf lowerGroup_map_subtype

theorem hasseArfChain_lowerGroup_of_isMulCommutative
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    HasseArfChain (lowerGroup R G) := by

  refine hasseArfChain_lowerGroup_of_forall_isCyclic_quotient (R := R) (G := G) ?_
  intro H _ hcycH
  haveI : IsDiscreteValuationRing (FixedPoints.subring R H) := isDiscreteValuationRing_fixedSubring
  obtain ⟨hf, hperf, hlo, hsep⟩ :=
    faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_fixedSubring (R := R) (G := G) H
  haveI := hf
  haveI := hperf
  haveI := hlo
  haveI := hsep
  haveI : IsCyclic (G ⧸ H) := hcycH
  exact hasseArfChain_lowerGroup_of_isCyclic
    (R := FixedPoints.subring R H) (G := G ⧸ H)

end

end

end Langlands.Ramification
