/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean`,
`Theorems/Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean`,
`P2M/Sol/S_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean`,
`Theorems/Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean`,
`P2M/Sol/S_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the six files (three statements and their proofs) are one module; the FLT proof name
spaces `P2MW.<file>.HasseArfTheta0` and `P2MW.<file>.IsLocalRing` are
`Langlands.Ramification.LowerGroupQuotients`; statements are on the Library's
`Langlands.Ramification.lowerGroup`; names follow the Library; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.Depth
import Langlands.LocalFactor.Ramification.FixedSubring
import Langlands.LocalFactor.Ramification.Uniformizer
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The quotients of consecutive lower ramification groups

The structure of the quotients of consecutive lower groups of a finite group acting on a discrete
valuation ring with perfect residue field `k`. The map `σ ↦ σ(ϖ)/ϖ mod m` is a homomorphism
`θ₀ : G_0 → k^×` with kernel `G_1`, so `G_0 / G_1` is cyclic, of order prime to the residue
characteristic. For `i ≥ 1` and `p ∈ m`, the `p`-th power of an element of `G_i` lies in `G_{i+1}`;
consequently `G_1` is a `p`-group when the action is faithful and the powers of `m` meet in `0`.
-/

namespace Langlands.Ramification

section

section

open IsLocalRing Polynomial

namespace LowerGroupQuotients

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

section Theta

variable {ϖ : R} (hϖ : Irreducible ϖ)

noncomputable def unifUnit (σ : G) : Rˣ :=
  (exists_smul_uniformizer_eq_unit_mul_of_irreducible hϖ σ).choose

theorem unifUnit_spec (σ : G) : σ • ϖ = (unifUnit hϖ σ : R) * ϖ :=
  (exists_smul_uniformizer_eq_unit_mul_of_irreducible hϖ σ).choose_spec

theorem unifUnit_one : unifUnit hϖ (1 : G) = 1 :=
  smul_uniformizer_unit_one hϖ.ne_zero (unifUnit_spec hϖ 1)

theorem coe_unifUnit_mul (σ τ : G) :
    (unifUnit hϖ (σ * τ) : R) = unifUnit hϖ σ * σ • (unifUnit hϖ τ : R) :=
  smul_uniformizer_unit_cocycle hϖ.ne_zero (unifUnit_spec hϖ σ)
    (unifUnit_spec hϖ τ) (unifUnit_spec hϖ (σ * τ))

theorem residue_smul_of_mem_zero {s : G} (hs : s ∈ lowerGroup R G 0) (x : R) :
    residue R (s • x) = residue R x := by
  rw [mem_lowerGroup] at hs
  have h := hs x
  rw [zero_add, pow_one] at h
  exact (Ideal.Quotient.eq).mpr h

noncomputable def theta0 : ↥(lowerGroup R G 0) →* (ResidueField R)ˣ where
  toFun s := Units.map (residue R : R →* ResidueField R) (unifUnit hϖ (s : G))
  map_one' := by
    rw [OneMemClass.coe_one, unifUnit_one, map_one]
  map_mul' s t := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul, Subgroup.coe_mul]
    rw [coe_unifUnit_mul, map_mul, residue_smul_of_mem_zero s.2]

theorem coe_theta0_apply (s : lowerGroup R G 0) :
    ((theta0 hϖ s : (ResidueField R)ˣ) : ResidueField R) = residue R (unifUnit hϖ (s : G)) :=
  rfl

theorem mem_ker_theta0_iff (s : lowerGroup R G 0) :
    s ∈ (theta0 hϖ).ker ↔ (s : G) • ϖ - ϖ ∈ IsLocalRing.maximalIdeal R ^ 2 := by
  rw [MonoidHom.mem_ker, Units.ext_iff, coe_theta0_apply, Units.val_one,
    ← (residue R).map_one, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hexp : (s : G) • ϖ - ϖ = ((unifUnit hϖ (s : G) : R) - 1) * ϖ := by
    rw [unifUnit_spec hϖ (s : G)]; ring
  rw [hexp, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, pow_two]
  exact (mul_dvd_mul_iff_right hϖ.ne_zero).symm

end Theta

section Core

variable [Finite G] [PerfectField (ResidueField R)]

theorem exists_invariant_sub_mem (r : R) :
    ∃ a : R, (∀ h ∈ lowerGroup R G 0, h • a = a) ∧
      r - a ∈ IsLocalRing.maximalIdeal R := by
  classical

  set H : Subgroup G := lowerGroup R G 0 with hH
  haveI : Fintype H := Fintype.ofFinite H
  let A : Subring R := FixedPoints.subring R H
  haveI : IsLocalHom (algebraMap A R) :=
    ⟨fun a h => (isUnit_fixedSubring_iff a).mpr h⟩
  have halg : ∀ a : A, algebraMap (ResidueField A) (ResidueField R) (residue A a) =
      residue R (a : R) := fun a => rfl

  let q : ℕ := ringExpChar (ResidueField A)
  haveI hqA : ExpChar (ResidueField A) q := inferInstance
  haveI hqR : ExpChar (ResidueField R) q :=
    expChar_of_injective_algebraMap (algebraMap (ResidueField A) (ResidueField R)).injective q
  set N : ℕ := Fintype.card H with hN
  have hNpos : 0 < N := Fintype.card_pos

  have key : ∀ x : ResidueField R,
      x ^ q ^ N ∈ (algebraMap (ResidueField A) (ResidueField R)).range := by
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x

    have hlifts : MulSemiringAction.charpoly H r ∈ Polynomial.lifts (algebraMap A R) := by
      refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
      exact ⟨⟨(MulSemiringAction.charpoly H r).coeff n,
        fun h => MulSemiringAction.smul_coeff_charpoly r n h⟩, rfl⟩
    obtain ⟨f, hfF, -, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts
      (MulSemiringAction.monic_charpoly H r)

    set fb : (ResidueField A)[X] := f.map (residue A) with hfb
    have hfbm : fb.Monic := hfm.map _

    have hmapF : (MulSemiringAction.charpoly H r).map (residue R) =
        (X - C (residue R r)) ^ N := by
      rw [MulSemiringAction.charpoly_eq, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      have hres : ∀ g : H, residue R ((g : G) • r) = residue R r := fun g =>
        residue_smul_of_mem_zero (R := R) (G := G) g.2 r
      simp only [Subgroup.smul_def, hres, Finset.prod_const, Finset.card_univ, hN]
    have hfbmap : fb.map (algebraMap (ResidueField A) (ResidueField R)) =
        (X - C (residue R r)) ^ N := by
      rw [hfb, Polynomial.map_map, ← hmapF, ← hfF, Polynomial.map_map]
      congr 1

    have hint : IsIntegral (ResidueField A) (residue R r) := by
      refine ⟨fb, hfbm, ?_⟩
      rw [← Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, hfbmap,
        Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_self, zero_pow hNpos.ne']
    have hroot : Polynomial.aeval (residue R r) fb = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hfbmap, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_pow hNpos.ne']
    have hdvd : minpoly (ResidueField A) (residue R r) ∣ fb := minpoly.dvd _ _ hroot
    have hfb0 : fb ≠ 0 := hfbm.ne_zero
    have hsep1 : (minpoly (ResidueField A) (residue R r)).natSepDegree = 1 := by
      refine le_antisymm ?_ ?_
      · calc (minpoly (ResidueField A) (residue R r)).natSepDegree
            ≤ fb.natSepDegree := Polynomial.natSepDegree_le_of_dvd _ _ hdvd hfb0
          _ = (fb.map (algebraMap (ResidueField A) (ResidueField R))).natSepDegree := by
              rw [Polynomial.natSepDegree_map]
          _ = 1 := by rw [hfbmap, Polynomial.natSepDegree_X_sub_C_pow, ite_eq_right hNpos.ne']
      · rw [Nat.one_le_iff_ne_zero, Polynomial.natSepDegree_ne_zero_iff]
        exact (minpoly.natDegree_pos hint).ne'
    obtain ⟨n, y, hny⟩ :=
      (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mp hsep1

    have hpow : residue R r ^ q ^ n = algebraMap (ResidueField A) (ResidueField R) y := by
      have h0 := minpoly.aeval (ResidueField A) (residue R r)
      rw [hny, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, sub_eq_zero] at h0
      exact h0
    have hdeg : q ^ n ≤ N := by
      have h1 : (minpoly (ResidueField A) (residue R r)).natDegree ≤ fb.natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hfb0
      rw [hny, Polynomial.natDegree_X_pow_sub_C, hfb, hfm.natDegree_map,
        ← hfm.natDegree_map (algebraMap A R), hfF,
        (MulSemiringAction.monic_charpoly H r).natDegree_map (residue R) |>.symm.trans
          (by rw [hmapF, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one])]
        at h1
      exact h1

    rcases (expChar_is_prime_or_one (ResidueField A) q) with hq | hq
    · have hn : n ≤ N := (Nat.lt_pow_self hq.one_lt).le.trans hdeg
      have : residue R r ^ q ^ N = (algebraMap (ResidueField A) (ResidueField R) y) ^ q ^ (N - n) := by
        rw [← hpow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hn]
      rw [this]
      exact pow_mem (RingHom.mem_range_self _ _) _
    · rw [hq, one_pow, pow_one]
      rw [hq, one_pow, pow_one] at hpow
      exact ⟨y, hpow.symm⟩

  set x : ResidueField R := (iterateFrobeniusEquiv (ResidueField R) q N).symm (residue R r) with hx
  have hxN : x ^ q ^ N = residue R r := by
    rw [← iterateFrobeniusEquiv_def, hx, RingEquiv.apply_symm_apply]
  obtain ⟨ybar, hy⟩ := key x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective ybar
  refine ⟨(a : R), fun h hh => a.2 ⟨h, hh⟩, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hxN, ← hy, halg]

theorem smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero
    {ϖ : R} (hϖ : Irreducible ϖ) {s : G} (hs : s ∈ lowerGroup R G 0) (x : R) :
    s • ϖ - ϖ ∣ s • x - x := by
  classical

  obtain ⟨x₀, hx₀⟩ := ENat.exists_eq_iInf (fun x : R => IsDiscreteValuationRing.addVal R (s • x - x))

  suffices hle : IsDiscreteValuationRing.addVal R (s • ϖ - ϖ) ≤
      IsDiscreteValuationRing.addVal R (s • x₀ - x₀) by
    refine IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hle.trans ?_)
    rw [hx₀]; exact iInf_le _ x

  obtain ⟨a, ha, hax⟩ := exists_invariant_sub_mem (R := R) (G := G) x₀
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hax
  obtain ⟨z, hz⟩ := hax
  have hx₀eq : x₀ = a + z * ϖ := by rw [← sub_eq_iff_eq_add', ← hz]
  have hsa : s • a = a := ha s hs
  have hdecomp : s • x₀ - x₀ = (s • ϖ - ϖ) * (s • z) + ϖ * (s • z - z) := by
    rw [hx₀eq, smul_add, smul_mul', hsa]; ring
  by_contra hlt
  push Not at hlt

  have h1 : IsDiscreteValuationRing.addVal R (s • x₀ - x₀) <
      IsDiscreteValuationRing.addVal R ((s • ϖ - ϖ) * (s • z)) := by
    rw [IsDiscreteValuationRing.addVal_mul]
    exact lt_of_lt_of_le hlt le_self_add
  have h2 : IsDiscreteValuationRing.addVal R (s • x₀ - x₀) <
      IsDiscreteValuationRing.addVal R (ϖ * (s • z - z)) := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    have hmin : IsDiscreteValuationRing.addVal R (s • x₀ - x₀) ≤
        IsDiscreteValuationRing.addVal R (s • z - z) := by rw [hx₀]; exact iInf_le _ z
    have hfin : IsDiscreteValuationRing.addVal R (s • x₀ - x₀) ≠ ⊤ := by
      intro htop; rw [htop] at hlt; exact not_top_lt hlt
    calc IsDiscreteValuationRing.addVal R (s • x₀ - x₀)
        < IsDiscreteValuationRing.addVal R (s • x₀ - x₀) + 1 := ENat.lt_add_one_iff hfin |>.mpr le_rfl
      _ = 1 + IsDiscreteValuationRing.addVal R (s • x₀ - x₀) := add_comm _ _
      _ ≤ 1 + IsDiscreteValuationRing.addVal R (s • z - z) := add_le_add le_rfl hmin
  have h12 := IsDiscreteValuationRing.addVal_add (R := R)
    (a := (s • ϖ - ϖ) * (s • z)) (b := ϖ * (s • z - z))
  rw [← hdecomp] at h12
  exact (lt_min h1 h2).not_ge h12

theorem mem_lowerGroup_iff_smul_uniformizer_sub_mem_pow
    {ϖ : R} (hϖ : Irreducible ϖ) {s : G} (hs : s ∈ lowerGroup R G 0) (i : ℕ) :
    s ∈ lowerGroup R G i ↔ s • ϖ - ϖ ∈ IsLocalRing.maximalIdeal R ^ (i + 1) := by
  refine ⟨fun h => (mem_lowerGroup.mp h) ϖ, fun h => ?_⟩
  rw [mem_lowerGroup]
  intro x
  obtain ⟨c, hc⟩ := smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero hϖ hs x
  rw [hc]
  exact Ideal.mul_mem_right _ _ h

theorem ker_theta0 {ϖ : R} (hϖ : Irreducible ϖ) :
    (theta0 (G := G) hϖ).ker = (lowerGroup R G 1).subgroupOf (lowerGroup R G 0) := by
  ext s
  rw [mem_ker_theta0_iff, Subgroup.mem_subgroupOf,
    mem_lowerGroup_iff_smul_uniformizer_sub_mem_pow hϖ s.2 1]

end Core

theorem not_dvd_card_of_charP {k : Type*} [Field k] {p : ℕ} (hp : p.Prime) (hpk : (p : k) = 0)
    (S : Subgroup kˣ) [Finite S] : ¬ p ∣ Nat.card S := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hgp : ((g : kˣ) : k) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one,
      Subgroup.coe_one, Units.val_one]
  have h1 : ((g : kˣ) : k) = 1 := by
    have h := sub_pow_char (R := k) ((g : kˣ) : k) 1
    rw [hgp, one_pow, sub_self, pow_eq_zero_iff hp.ne_zero, sub_eq_zero] at h
    exact h
  have hg1 : g = 1 := Subtype.ext (Units.ext h1)
  rw [hg1, orderOf_one] at hg
  exact hp.one_lt.ne' hg.symm

end LowerGroupQuotients

open LowerGroupQuotients in
theorem exists_monoidHom_lowerGroup_zero_residueField_units
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)] :
    (∃ θ : ↥(lowerGroup R G 0) →* (IsLocalRing.ResidueField R)ˣ,
        θ.ker = (lowerGroup R G 1).subgroupOf
          (lowerGroup R G 0)) ∧
    IsCyclic (↥(lowerGroup R G 0) ⧸
        (lowerGroup R G 1).subgroupOf
          (lowerGroup R G 0)) ∧
    (∀ p : ℕ, p.Prime → (p : R) ∈ IsLocalRing.maximalIdeal R →
        ¬ p ∣ (lowerGroup R G 1).relIndex
          (lowerGroup R G 0)) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hker := LowerGroupQuotients.ker_theta0 (R := R) (G := G) hϖ
  set θ := LowerGroupQuotients.theta0 (R := R) (G := G) hϖ with hθ

  haveI : Finite θ.range := Finite.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  haveI hcyc : IsCyclic θ.range := inferInstance
  refine ⟨⟨θ, hker⟩, ?_, ?_⟩
  ·
    have e : ↥(lowerGroup R G 0) ⧸
        (lowerGroup R G 1).subgroupOf
          (lowerGroup R G 0) ≃* θ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange θ)
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  · intro p hp hpR
    have hrel : (lowerGroup R G 1).relIndex
        (lowerGroup R G 0) = Nat.card θ.range := by
      unfold Subgroup.relIndex
      rw [← hker, Subgroup.index_ker]
    rw [hrel]
    have hpk : (p : IsLocalRing.ResidueField R) = 0 := by
      rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]
      exact hpR
    exact LowerGroupQuotients.not_dvd_card_of_charP hp hpk θ.range

end

end

section

section

open scoped Pointwise commutatorElement

namespace LowerGroupQuotients
open IsLocalRing (ResidueField maximalIdeal residue)
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem smul_mem_maximalIdeal_pow_of_mem {σ : G} {j : ℕ} {a : R}
    (ha : a ∈ (maximalIdeal R) ^ j) : σ • a ∈ (maximalIdeal R) ^ j := by
  have h := Ideal.smul_mem_pointwise_smul σ a ((maximalIdeal R) ^ j) ha
  rwa [pointwise_smul_maximalIdeal_pow] at h

theorem smul_sub_mem_maximalIdeal_pow_add_of_mem_lowerGroup
    {i : ℕ} {σ : G} (hσ : σ ∈ lowerGroup R G i)
    {j : ℕ} {y : R} (hy : y ∈ (maximalIdeal R) ^ j) :
    σ • y - y ∈ (maximalIdeal R) ^ (i + j) := by
  induction j generalizing y with
  | zero =>
    exact Ideal.pow_le_pow_right (by omega) (hσ y)
  | succ j ih =>
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun u v hu hv => ?_)
    ·
      have hexp : σ • (a * b) - a * b = (σ • a) * (σ • b - b) + (σ • a - a) * b := by
        rw [smul_mul']
        ring
      rw [hexp]
      refine Ideal.add_mem _ ?_ ?_
      · have h1 : (σ • a) * (σ • b - b) ∈ (maximalIdeal R) ^ j * (maximalIdeal R) ^ (i + 1) :=
          Ideal.mul_mem_mul (smul_mem_maximalIdeal_pow_of_mem ha) (hσ b)
        rw [← pow_add] at h1
        exact Ideal.pow_le_pow_right (by omega) h1
      · have h2 : (σ • a - a) * b ∈ (maximalIdeal R) ^ (i + j) * maximalIdeal R :=
          Ideal.mul_mem_mul (ih ha) hb
        rw [← pow_succ] at h2
        exact Ideal.pow_le_pow_right (by omega) h2
    · have hexp : σ • (u + v) - (u + v) = (σ • u - u) + (σ • v - v) := by
        rw [smul_add]
        ring
      rw [hexp]
      exact Ideal.add_mem _ hu hv

end LowerGroupQuotients

open IsLocalRing LowerGroupQuotients in
theorem pow_mem_lowerGroup_succ {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    {p : ℕ} (hp : (p : R) ∈ maximalIdeal R) {i : ℕ} (hi : 1 ≤ i) {σ : G}
    (hσ : σ ∈ lowerGroup R G i) :
    σ ^ p ∈ lowerGroup R G (i + 1) := by
  rw [mem_lowerGroup]
  intro x
  set y : R := σ • x - x with hy
  have hyM : y ∈ (maximalIdeal R) ^ (i + 1) := hσ x

  have key : ∀ n : ℕ, σ ^ n • x - x - n • y ∈ (maximalIdeal R) ^ (i + 1 + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpow : σ ^ n ∈ lowerGroup R G i := pow_mem hσ n
      have hstep : σ ^ n • y - y ∈ (maximalIdeal R) ^ (i + 1 + 1) := by
        have h2 := LowerGroupQuotients.smul_sub_mem_maximalIdeal_pow_add_of_mem_lowerGroup hpow hyM
        exact Ideal.pow_le_pow_right (by omega) h2
      have hσx : σ • x = x + y := by
        rw [hy]
        ring
      have hrw : σ ^ (n + 1) • x - x - (n + 1) • y
          = (σ ^ n • x - x - n • y) + (σ ^ n • y - y) := by
        rw [pow_succ, mul_smul, hσx, smul_add, succ_nsmul]
        ring
      rw [hrw]
      exact Ideal.add_mem _ ih hstep
  have hpy : (p : ℕ) • y ∈ (maximalIdeal R) ^ (i + 1 + 1) := by
    rw [nsmul_eq_mul, pow_succ']
    exact Ideal.mul_mem_mul hp hyM
  have hfin : σ ^ p • x - x = (σ ^ p • x - x - (p : ℕ) • y) + (p : ℕ) • y := by
    ring
  rw [hfin]
  exact Ideal.add_mem _ (key p) hpy

end

end

section

section

theorem isPGroup_lowerGroup_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hsep : ⨅ n, IsLocalRing.maximalIdeal R ^ n = ⊥) :
    IsPGroup p (lowerGroup R G 1) := by
  obtain ⟨N, hN⟩ := exists_lowerGroup_eq_bot_of_iInf_eq_bot (R := R) (G := G) hsep
  intro σ
  refine ⟨N, ?_⟩
  have key : ∀ k : ℕ, (σ : G) ^ p ^ k ∈ lowerGroup R G (k + 1) := by
    intro k
    induction k with
    | zero => simpa using σ.2
    | succ k ih =>
      rw [pow_succ, pow_mul]
      exact pow_mem_lowerGroup_succ hp (Nat.succ_le_succ (Nat.zero_le k)) ih
  have h := key N
  rw [hN (N + 1) (Nat.le_succ N), Subgroup.mem_bot] at h
  exact Subtype.ext (by simpa using h)

end

end

end Langlands.Ramification
