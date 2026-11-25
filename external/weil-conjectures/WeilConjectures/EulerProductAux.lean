/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.LinearCombination
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.WellKnown

public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

/-!
# Power series lemmas for Euler products

This file provides the formal power series input for the Euler product expansion of the
zeta function of a variety over a finite field (`WeilConjectures.EulerProduct`):
elementary facts about the geometric series `(1 - X ^ d)⁻¹ ∈ ℚ⟦X⟧`, the logarithmic
derivative of finite products of such series, a uniqueness lemma for solutions of the
differential equation `X * F' = A * F`, and the coefficientwise computation of infinite
products `∏ (1 - X ^ d i)⁻¹` in the coefficientwise (product) topology, for families of
exponents `d` such that `{i | d i ≤ n}` is finite for all `n`.
-/

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

namespace PowerSeries

section Geometric

private lemma constantCoeff_one_sub_X_pow_eq_one {d : ℕ} (hd : d ≠ 0) :
    constantCoeff (1 - X ^ d : ℚ⟦X⟧) = 1 := by
  simp [zero_pow hd]

private lemma one_sub_X_pow_mul_inv {d : ℕ} (hd : d ≠ 0) :
    ((1 - X ^ d) * (1 - X ^ d)⁻¹ : ℚ⟦X⟧) = 1 :=
  PowerSeries.mul_inv_cancel _
    (by rw [constantCoeff_one_sub_X_pow_eq_one hd]; exact one_ne_zero)

private lemma dvd_iff_dvd_sub {d n : ℕ} (hle : d ≤ n) : d ∣ n ↔ d ∣ n - d := by
  constructor
  · intro h
    exact Nat.dvd_sub h dvd_rfl
  · intro h
    have h2 := dvd_add h (dvd_refl d)
    rwa [Nat.sub_add_cancel hle] at h2

theorem constantCoeff_inv_one_sub_X_pow {d : ℕ} (hd : d ≠ 0) :
    constantCoeff ((1 - X ^ d)⁻¹ : ℚ⟦X⟧) = 1 := by
  rw [constantCoeff_inv, constantCoeff_one_sub_X_pow_eq_one hd, inv_one]

theorem inv_one_sub_X_pow_sub_one {d : ℕ} (hd : d ≠ 0) :
    ((1 - X ^ d)⁻¹ : ℚ⟦X⟧) - 1 = X ^ d * (1 - X ^ d)⁻¹ := by
  linear_combination one_sub_X_pow_mul_inv hd

/-- The logarithmic derivative of the geometric series `(1 - X ^ d)⁻¹`:
`X * ((1 - X ^ d)⁻¹)' = (∑ d * X ^ (d * m)) * (1 - X ^ d)⁻¹`. -/
theorem X_mul_derivative_inv_one_sub_X_pow {d : ℕ} (hd : d ≠ 0) :
    X * derivative (R := ℚ) ((1 - X ^ d)⁻¹ : ℚ⟦X⟧) =
      (mk fun n ↦ if d ∣ n ∧ n ≠ 0 then (d : ℚ) else 0) * (1 - X ^ d)⁻¹ := by
  have hC : (C (d : ℚ) : ℚ⟦X⟧) = ((d : ℕ) : ℚ⟦X⟧) := map_natCast (C : ℚ →+* ℚ⟦X⟧) d
  have key : (mk fun n ↦ if d ∣ n ∧ n ≠ 0 then (d : ℚ) else 0) =
      ((d : ℕ) : ℚ⟦X⟧) * (X ^ d * (1 - X ^ d)⁻¹) := by
    rw [← hC, inv_one_sub_X_pow_eq_mk hd]
    ext n
    simp only [coeff_mk, coeff_C_mul, coeff_X_pow_mul']
    by_cases hle : d ≤ n
    · have hn : n ≠ 0 := by omega
      rw [ite_eq_left hle]
      by_cases hdvd : d ∣ n
      · rw [ite_eq_left ⟨hdvd, hn⟩, ite_eq_left ((dvd_iff_dvd_sub hle).mp hdvd), mul_one]
      · rw [ite_eq_right fun hc ↦ hdvd hc.1,
          ite_eq_right fun hc ↦ hdvd ((dvd_iff_dvd_sub hle).mpr hc), mul_zero]
    · rw [ite_eq_right hle, mul_zero, ite_eq_right]
      rintro ⟨hdvd, hn⟩
      exact hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)
  have hmul := one_sub_X_pow_mul_inv hd
  have hder : derivative (R := ℚ) ((1 - X ^ d) * (1 - X ^ d)⁻¹ : ℚ⟦X⟧) =
      derivative (R := ℚ) (1 : ℚ⟦X⟧) := by
    rw [hmul]
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul, map_sub,
    derivative_pow, derivative_X, mul_one, Derivation.map_one_eq_zero, zero_sub] at hder
  rw [key]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hder
  linear_combination (X * ((1 - X ^ (e + 1))⁻¹ : ℚ⟦X⟧)) * hder -
    (X * derivative (R := ℚ) ((1 - X ^ (e + 1))⁻¹ : ℚ⟦X⟧)) * hmul

/-- The logarithmic derivative of a finite product of geometric series is the sum of
the logarithmic derivatives of the factors. -/
theorem X_mul_derivative_prod_inv_one_sub_X_pow {ι : Type*} (d : ι → ℕ) (S : Finset ι)
    (hd : ∀ i ∈ S, d i ≠ 0) :
    X * derivative (R := ℚ) (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
      (∑ i ∈ S, mk fun n ↦ if d i ∣ n ∧ n ≠ 0 then (d i : ℚ) else 0) *
        ∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have h4 := X_mul_derivative_inv_one_sub_X_pow (hd a (Finset.mem_insert_self a S))
    have ihS := ih fun i hi ↦ hd i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
    linear_combination ((1 - X ^ d a)⁻¹ : ℚ⟦X⟧) * ihS +
      (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) * h4

end Geometric

section Uniqueness

/-- Uniqueness of solutions of the differential equation `X * F' = A * F` over a field of
characteristic zero: two power series with the same constant coefficient satisfying
logarithmic differential equations whose right hand sides agree up to order `m` agree up to
order `m`. The coefficients are determined by the recursion
`n * c n = ∑ j < n, a (n - j) * c j`. -/
theorem coeff_eq_of_X_mul_derivative_eq {R : Type*} [Field R] [CharZero R] {F G A B : R⟦X⟧}
    (hF : X * derivative (R := R) F = A * F) (hG : X * derivative (R := R) G = B * G)
    (h0 : constantCoeff F = constantCoeff G) (hA : constantCoeff A = 0)
    {m : ℕ} (hAB : ∀ i ≤ m, coeff i A = coeff i B) :
    ∀ n ≤ m, coeff n F = coeff n G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain _ | j := n
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
      exact h0
    · have hA0 : coeff 0 A = 0 := by
        rw [coeff_zero_eq_constantCoeff_apply]; exact hA
      have hB0 : coeff 0 B = 0 := by
        rw [← hAB 0 (Nat.zero_le m)]; exact hA0
      have hFc : coeff (j + 1) F * ((j : R) + 1) =
          ∑ p ∈ antidiagonal (j + 1), coeff p.1 A * coeff p.2 F := by
        rw [← coeff_derivative, ← coeff_succ_X_mul, hF, coeff_mul]
      have hGc : coeff (j + 1) G * ((j : R) + 1) =
          ∑ p ∈ antidiagonal (j + 1), coeff p.1 B * coeff p.2 G := by
        rw [← coeff_derivative, ← coeff_succ_X_mul, hG, coeff_mul]
      have hsum : ∑ p ∈ antidiagonal (j + 1), coeff p.1 A * coeff p.2 F =
          ∑ p ∈ antidiagonal (j + 1), coeff p.1 B * coeff p.2 G := by
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [mem_antidiagonal] at hp
        rcases eq_or_ne p.1 0 with h1 | h1
        · rw [h1, hA0, hB0, zero_mul, zero_mul]
        · rw [hAB p.1 (by omega), ih p.2 (by omega) (by omega)]
      have hcast : ((j : R) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      exact mul_right_cancel₀ hcast (hFc.trans (hsum.trans hGc.symm))

end Uniqueness

section Tprod

variable {ι : Type*} {d : ι → ℕ}

private lemma X_pow_succ_dvd_prod_inv_one_sub_X_pow_sub_one {n : ℕ} {U : Finset ι}
    (hU : ∀ i ∈ U, n < d i) :
    (X : ℚ⟦X⟧) ^ (n + 1) ∣ (∏ i ∈ U, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) - 1 := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | insert a U ha ih =>
    have h1 : (X : ℚ⟦X⟧) ^ (n + 1) ∣ ((1 - X ^ d a)⁻¹ : ℚ⟦X⟧) - 1 := by
      rw [inv_one_sub_X_pow_sub_one
        (by have := hU a (Finset.mem_insert_self a U); omega)]
      exact dvd_mul_of_dvd_left (pow_dvd_pow X (hU a (Finset.mem_insert_self a U))) _
    have h2 := ih fun i hi ↦ hU i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha]
    have heq : ((1 - X ^ d a)⁻¹ : ℚ⟦X⟧) * ∏ i ∈ U, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧) - 1 =
        (1 - X ^ d a)⁻¹ * ((∏ i ∈ U, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) - 1) +
          ((1 - X ^ d a)⁻¹ - 1) := by
      ring
    rw [heq]
    exact dvd_add (Dvd.dvd.mul_left h2 _) h1

private lemma coeff_mul_eq_of_X_pow_dvd_sub_one {F H : ℚ⟦X⟧} {n : ℕ}
    (hH : (X : ℚ⟦X⟧) ^ (n + 1) ∣ H - 1) :
    coeff n (H * F) = coeff n F := by
  obtain ⟨c, hc⟩ := hH
  have heq : H * F = X ^ (n + 1) * (c * F) + F := by
    have hHeq : H = X ^ (n + 1) * c + 1 := by linear_combination hc
    rw [hHeq]; ring
  rw [heq, map_add, coeff_X_pow_mul', ite_eq_right (by omega), zero_add]

/-- Factors of degree greater than `n` do not affect the `n`-th coefficient of a product
of geometric series. -/
theorem coeff_prod_inv_one_sub_X_pow_congr {S T : Finset ι} (hTS : T ⊆ S) {n : ℕ}
    (h : ∀ i ∈ S, i ∉ T → n < d i) :
    coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
      coeff n (∏ i ∈ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by
  classical
  rw [← Finset.prod_sdiff hTS]
  exact coeff_mul_eq_of_X_pow_dvd_sub_one
    (X_pow_succ_dvd_prod_inv_one_sub_X_pow_sub_one fun i hi ↦
      h i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2)

open WithPiTopology in
/-- A family of geometric series `(1 - X ^ d i)⁻¹` with only finitely many exponents
below any given bound is multipliable in the coefficientwise topology. -/
theorem multipliable_inv_one_sub_X_pow (hd : ∀ i, d i ≠ 0)
    (hfin : ∀ n, {i | d i ≤ n}.Finite) :
    Multipliable fun i ↦ ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧) := by
  classical
  have hsum : Summable fun s : Finset ι ↦
      ∏ i ∈ s, (((1 - X ^ d i)⁻¹ : ℚ⟦X⟧) - 1) := by
    rw [summable_iff_summable_coeff]
    intro n
    apply summable_of_hasFiniteSupport
    apply ((hfin n).toFinset.powerset.finite_toSet.subset)
    intro s hs
    rw [Function.mem_support] at hs
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro j hj
    rw [Set.Finite.mem_toFinset]
    by_contra hjn
    rw [Set.mem_ofPred_eq, not_le] at hjn
    apply hs
    have h1 : (X : ℚ⟦X⟧) ^ (n + 1) ∣ ((1 - X ^ d j)⁻¹ : ℚ⟦X⟧) - 1 := by
      rw [inv_one_sub_X_pow_sub_one (hd j)]
      exact dvd_mul_of_dvd_left (pow_dvd_pow X hjn) _
    exact X_pow_dvd_iff.mp
      (h1.trans (Finset.dvd_prod_of_mem (fun i ↦ ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧) - 1) hj)) n
      (Nat.lt_succ_self n)
  exact (multipliable_one_add_of_summable_prod hsum).congr fun i ↦ by ring

open WithPiTopology in
/-- The `n`-th coefficient of the infinite product `∏ (1 - X ^ d i)⁻¹` equals the `n`-th
coefficient of the finite subproduct over any finite set containing all indices with
`d i ≤ n`. -/
theorem coeff_tprod_inv_one_sub_X_pow (hd : ∀ i, d i ≠ 0)
    (hfin : ∀ n, {i | d i ≤ n}.Finite) (n : ℕ) {T : Finset ι}
    (hT : ∀ i, d i ≤ n → i ∈ T) :
    coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
      coeff n (∏ i ∈ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by
  classical
  set T₀ : Finset ι := (hfin n).toFinset with hT₀
  have hsub : T₀ ⊆ T := fun i hi ↦ hT i ((hfin n).mem_toFinset.mp hi)
  have hTT₀ : ∀ i ∈ T, i ∉ T₀ → n < d i := by
    intro i _ hni
    by_contra hle
    exact hni ((hfin n).mem_toFinset.mpr (not_lt.mp hle))
  have hmul := multipliable_inv_one_sub_X_pow hd hfin
  have htend : Filter.Tendsto
      (fun s : Finset ι ↦ coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)))
      Filter.atTop (nhds (coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)))) :=
    ((continuous_coeff ℚ n).tendsto _).comp hmul.hasProd
  have heq : Filter.EventuallyEq Filter.atTop
      (fun s : Finset ι ↦ coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)))
      (fun _ ↦ coeff n (∏ i ∈ T₀, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧))) := by
    filter_upwards [Filter.eventually_ge_atTop T₀] with s hs
    refine coeff_prod_inv_one_sub_X_pow_congr hs fun i _ hni ↦ ?_
    by_contra hle
    exact hni ((hfin n).mem_toFinset.mpr (not_lt.mp hle))
  have h1 : coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
      coeff n (∏ i ∈ T₀, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) :=
    tendsto_nhds_unique htend (Filter.Tendsto.congr' heq.symm tendsto_const_nhds)
  rw [h1]
  exact (coeff_prod_inv_one_sub_X_pow_congr hsub hTT₀).symm

open WithPiTopology in
/-- **Coefficients of an Euler product.** If `dᵢ ≥ 1` for all `i` and only finitely many `dᵢ`
are at most any given bound, the `n`-th coefficient of `∏ᵢ (1 - T^{dᵢ})⁻¹` is the number of
finitely supported `m : ι →₀ ℕ` with `∑ᵢ mᵢ dᵢ = n`. -/
theorem coeff_tprod_inv_one_sub_X_pow_eq_natCard (hd : ∀ i, d i ≠ 0)
    (hfin : ∀ n, {i | d i ≤ n}.Finite) (n : ℕ) :
    coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
      Nat.card {m : ι →₀ ℕ // (m.sum fun i k ↦ k * d i) = n} := by
  classical
  set T : Finset ι := (hfin n).toFinset with hT_def
  have hT : ∀ i, d i ≤ n → i ∈ T := fun i hi ↦ by simpa [hT_def] using hi
  rw [coeff_tprod_inv_one_sub_X_pow hd hfin n hT, coeff_prod]
  simp only [inv_one_sub_X_pow_eq_mk (hd _), coeff_mk]
  rw [Finset.sum_congr rfl fun l _ ↦ Finset.prod_boole, Finset.sum_boole]
  congr 1
  -- the families `m` correspond to the `l = m d` in the antidiagonal divisible by `d`
  -- the support of an admissible `m` lies in `T`
  have hsupp (m : ι →₀ ℕ) (hm : (m.sum fun i k ↦ k * d i) = n) : m.support ⊆ T := by
    intro i hi
    refine hT i ?_
    have hle : m i * d i ≤ m.sum fun i k ↦ k * d i :=
      Finset.single_le_sum (f := fun i ↦ m i * d i) (fun _ _ ↦ Nat.zero_le _) hi
    have : 1 ≤ m i := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
    nlinarith
  let toL (m : ι →₀ ℕ) : ι →₀ ℕ :=
    Finsupp.ofSupportFinite (fun i ↦ m i * d i) (m.hasFiniteSupport.subset fun i hi ↦ by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hi
      exact hi.1)
  let toM (l : ι →₀ ℕ) : ι →₀ ℕ :=
    Finsupp.ofSupportFinite (fun i ↦ l i / d i) (l.hasFiniteSupport.subset fun i hi ↦ by
      simp only [Function.mem_support, ne_eq] at hi ⊢
      intro h
      exact hi (by rw [h, Nat.zero_div]))
  have htoL (m : ι →₀ ℕ) (i : ι) : toL m i = m i * d i := rfl
  have htoM (l : ι →₀ ℕ) (i : ι) : toM l i = l i / d i := rfl
  have hsumT (m : ι →₀ ℕ) (hm : m.support ⊆ T) :
      (m.sum fun i k ↦ k * d i) = ∑ i ∈ T, toL m i := by
    rw [Finsupp.sum, Finset.sum_subset hm fun i _ hi ↦ by
      rw [Finsupp.notMem_support_iff.1 hi, zero_mul]]
    rfl
  refine (Nat.card_eq_finsetCard _).symm.trans (Nat.card_congr ?_)
  exact
    { toFun l := ⟨toM l.1, by
        obtain ⟨hl, hdvd⟩ := Finset.mem_filter.1 l.2
        rw [Finset.mem_finsuppAntidiag] at hl
        have hlm : toL (toM l.1) = l.1 := by
          ext i
          rw [htoL, htoM]
          by_cases hi : i ∈ T
          · exact Nat.div_mul_cancel (hdvd i hi)
          · rw [Finsupp.notMem_support_iff.1 fun h ↦ hi (hl.2 h), Nat.zero_div, zero_mul]
        have hsub : (toM l.1).support ⊆ T := fun i hi ↦ by
          by_contra hiT
          apply Finsupp.mem_support_iff.1 hi
          rw [htoM, Finsupp.notMem_support_iff.1 fun h ↦ hiT (hl.2 h), Nat.zero_div]
        rw [hsumT _ hsub, hlm, hl.1]⟩
      invFun m := ⟨toL m.1, by
        have hsub := hsupp m.1 m.2
        refine Finset.mem_filter.2 ⟨Finset.mem_finsuppAntidiag.2 ⟨?_, fun i hi ↦ ?_⟩,
          fun i _ ↦ ⟨m.1 i, by rw [htoL, mul_comm]⟩⟩
        · rw [← hsumT _ hsub, m.2]
        · refine hsub (Finsupp.mem_support_iff.2 fun h ↦ ?_)
          apply Finsupp.mem_support_iff.1 hi
          rw [htoL, h, zero_mul]⟩
      left_inv l := by
        obtain ⟨hl, hdvd⟩ := Finset.mem_filter.1 l.2
        rw [Finset.mem_finsuppAntidiag] at hl
        refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
        change toL (toM l.1) i = l.1 i
        rw [htoL, htoM]
        by_cases hi : i ∈ T
        · exact Nat.div_mul_cancel (hdvd i hi)
        · rw [Finsupp.notMem_support_iff.1 fun h ↦ hi (hl.2 h), Nat.zero_div, zero_mul]
      right_inv m := by
        refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
        change toM (toL m.1) i = m.1 i
        rw [htoM, htoL, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (hd i))] }

end Tprod

end PowerSeries
