/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Inverse
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Euler products with bounded local roots

This file contains the analytic part (Steps 1–3) of the proof of
`proposition-weights-j-boundary-points--1`, stated for an abstract Euler product, so that it applies
both to Weil representations and to Weil sheaves.

Let `J` be a set of "closed points", each with a degree `e x ≥ 1`, only finitely many of any
bounded degree, and with at most `A qⁿ` points of degree `n`. At every point let
`P_x (T) = ∏_{a ∈ M x} (1 - a T ^ {e x})` be a local polynomial with at most `d` local roots
`a`, all of absolute value at most `c ^ {e x}`. Then the inverse of the Euler product
`∏_x P_x (T)⁻¹` converges on the disc `|T| < (q c)⁻¹`
(`PowerSeries.le_radius_inv_tprod_inv_eulerPoly`): its coefficient of degree `n` is that of the
finite product of the `P_x` over the points of degree at most `n`, whose weighted `ℓ¹`-norm
`∑ₙ |aₙ| rⁿ` is at most `∏_x (1 + (c r) ^ {e x}) ^ d ≤ exp (d A ∑ₙ (q c r)ⁿ)`.

Consequently, if this Euler product times `∏_{b ∈ S} (1 - b T)` is `P · B` for polynomials `P`
and `B`, where all `|b| ≤ q c`, then `B` has no zero in that disc
(`PowerSeries.one_le_mul_norm_of_tprod_mul_eq_mul`).

## Main definitions

- `PowerSeries.eulerPoly`: the polynomial `∏_{a ∈ M} (1 - a T ^ e)`.

## Main statements

- `PowerSeries.le_radius_inv_tprod_inv_eulerPoly`: the radius of convergence of the inverse of
  an Euler product with bounded local roots.
- `PowerSeries.one_le_mul_norm_of_tprod_mul_eq_mul`: the zeros of `B` lie outside the disc.
- `PowerSeries.eq_tprod_mul_prod_of_forall_coeff_prod_eq`: an identity of locally finite Euler
  products, given coefficientwise, splits off finitely many factors.
-/

@[expose] public section

open scoped PowerSeries.WithPiTopology NNReal ENNReal

namespace PowerSeries

section Split

variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]

/-- An identity of locally finite Euler products, given coefficientwise. Let `f x` be power
series with `f x ≡ 1` modulo `X ^ (n + 1)` for all `x` outside a finite set `S n`, and suppose
that `G` has, in every degree `n`, the coefficient of the finite product of the `f x` over every
finite set containing `S n`. Then, for every set `T`
of indices with finite complement, `G` is the product of `∏'_{x ∈ T} f x` and the finitely many
`f x` with `x ∉ T`. -/
theorem eq_tprod_mul_prod_of_forall_coeff_prod_eq {J : Type*} {f : J → R⟦X⟧}
    (S : ℕ → Finset J) (hS : ∀ n, ∀ x ∉ S n, X ^ (n + 1) ∣ f x - 1) {G : R⟦X⟧}
    (hG : ∀ n (s : Finset J), S n ⊆ s → coeff n (∏ x ∈ s, f x) = coeff n G)
    {T : Set J} (hT : Tᶜ.Finite) :
    G = (∏' x : T, f x.1) * ∏ x ∈ hT.toFinset, f x := by
  classical
  ext n
  -- the indices of `T` in `S n`
  set s' : Finset T := (S n).subtype (· ∈ T)
  have hS' (m : ℕ) : ∀ x : T, x ∉ (S m).subtype (· ∈ T) → X ^ (m + 1) ∣ f x.1 - 1 :=
    fun x hx ↦ hS m x.1 fun h ↦ hx (Finset.mem_subtype.2 h)
  have hs' : ∀ x : T, x ∉ s' → X ^ (n + 1) ∣ f x.1 - 1 := hS' n
  have hcoeff (k : ℕ) (hk : k ≤ n) : coeff k (∏' x : T, f x.1) = coeff k (∏ x ∈ s', f x.1) :=
    WithPiTopology.coeff_tprod_of_X_pow_dvd_sub_one (fun m ↦ (S m).subtype (· ∈ T)) hS' s'
      hs' hk
  have hdvd : X ^ (n + 1) ∣ (∏' x : T, f x.1) - ∏ x ∈ s', f x.1 := by
    rw [X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hcoeff k (Nat.lt_succ_iff.1 hk), sub_self]
  -- the finite set `S n ∪ Tᶜ`
  set s : Finset J := S n ∪ hT.toFinset
  have hsplit : ∏ x ∈ s, f x = (∏ x ∈ s', f x.1) * ∏ x ∈ hT.toFinset, f x := by
    have hdisj : Disjoint (s'.map (Function.Embedding.subtype _)) hT.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
      exact (hT.mem_toFinset.1 hx') y.2
    have hunion : s = s'.map (Function.Embedding.subtype _) ∪ hT.toFinset := by
      ext x
      simp only [s, s', Finset.mem_union, Finset.mem_map, Finset.mem_subtype,
        Function.Embedding.coe_subtype, Set.Finite.mem_toFinset, Set.mem_compl_iff]
      constructor
      · rintro (h | h)
        · by_cases hxT : x ∈ T
          · exact Or.inl ⟨⟨x, hxT⟩, h, rfl⟩
          · exact Or.inr hxT
        · exact Or.inr h
      · rintro (⟨y, hy, rfl⟩ | h)
        · exact Or.inl hy
        · exact Or.inr h
    rw [hunion, Finset.prod_union hdisj, Finset.prod_map]
    rfl
  rw [← hG n s Finset.subset_union_left, hsplit]
  obtain ⟨g, hg⟩ := hdvd
  have : (∏' x : T, f x.1) * ∏ x ∈ hT.toFinset, f x =
      (∏ x ∈ s', f x.1) * ∏ x ∈ hT.toFinset, f x + X ^ (n + 1) * (g * ∏ x ∈ hT.toFinset, f x) := by
    rw [← mul_assoc, ← hg]
    ring
  rw [this, map_add, coeff_X_pow_mul', ite_eq_right (by omega), add_zero]

end Split

section Radius


/-- The polynomial `∏_{a ∈ M} (1 - a T ^ e)`: the local polynomial at a closed point of degree
`e` with local roots `M`. -/
noncomputable def eulerPoly (M : Multiset ℂ) (e : ℕ) : Polynomial ℂ :=
  ((M.map fun a ↦ 1 - Polynomial.C a * Polynomial.X).prod).comp (Polynomial.X ^ e)

theorem eulerPoly_coeff_zero (M : Multiset ℂ) {e : ℕ} (he : e ≠ 0) :
    (eulerPoly M e).coeff 0 = 1 := by
  rw [eulerPoly, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_pow,
    Polynomial.eval_X, zero_pow he, Polynomial.eval_multiset_prod, Multiset.map_map]
  exact Multiset.prod_eq_one fun a ha ↦ by
    obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 ha
    simp

theorem constantCoeff_eulerPoly (M : Multiset ℂ) {e : ℕ} (he : e ≠ 0) :
    constantCoeff ((eulerPoly M e : Polynomial ℂ) : ℂ⟦X⟧) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, eulerPoly_coeff_zero M he]

/-- The local polynomial `∏_{a ∈ M} (1 - a T ^ e)` is `1` modulo `T ^ e`. -/
theorem X_pow_dvd_eulerPoly_sub_one (M : Multiset ℂ) (e : ℕ) :
    (X : ℂ⟦X⟧) ^ e ∣ ((eulerPoly M e : Polynomial ℂ) : ℂ⟦X⟧) - 1 := by
  have hP : (Polynomial.X : Polynomial ℂ) ∣ (M.map fun a ↦ 1 - Polynomial.C a * Polynomial.X).prod
      - 1 := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.coeff_one_zero,
      Multiset.prod_eq_one fun a ha ↦ by
        obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 ha
        simp, sub_self]
  obtain ⟨Q, hQ⟩ := hP
  have hQ' : (Polynomial.X : Polynomial ℂ) ^ e ∣ eulerPoly M e - 1 :=
    ⟨Q.comp (Polynomial.X ^ e), by
      have hc : ((M.map fun a ↦ 1 - Polynomial.C a * Polynomial.X).prod - 1).comp
          (Polynomial.X ^ e) = eulerPoly M e - 1 := by
        rw [Polynomial.sub_comp, Polynomial.one_comp, eulerPoly]
      rw [← hc, hQ, Polynomial.mul_comp, Polynomial.X_comp]⟩
  have h := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) hQ'
  simpa only [map_pow, map_sub, map_one, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X] using h

/-- The inverse local factor `(∏_{a ∈ M} (1 - a T ^ e))⁻¹` is `1` modulo `T ^ e`. -/
theorem X_pow_dvd_inv_eulerPoly_sub_one (M : Multiset ℂ) {e : ℕ} (he : e ≠ 0) :
    (X : ℂ⟦X⟧) ^ e ∣ ((eulerPoly M e : Polynomial ℂ) : ℂ⟦X⟧)⁻¹ - 1 := by
  have h := X_pow_dvd_inv_sub_inv (n := e)
    (by rw [constantCoeff_eulerPoly M he]; exact one_ne_zero) (by simp)
    (X_pow_dvd_eulerPoly_sub_one M e)
  rwa [inv_one] at h

/-- The weighted `ℓ¹`-norm `∑ₙ ‖aₙ‖ rⁿ` of a complex polynomial. -/
private noncomputable def wnorm (r : ℝ) (f : Polynomial ℂ) : ℝ :=
  ∑' n, ‖f.coeff n‖ * r ^ n

private theorem summable_wnorm (r : ℝ) (f : Polynomial ℂ) :
    Summable fun n ↦ ‖f.coeff n‖ * r ^ n :=
  summable_of_ne_finset_zero (s := Finset.range (f.natDegree + 1)) fun n hn ↦ by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
      norm_zero, zero_mul]

private theorem norm_coeff_mul_pow_le_wnorm {r : ℝ} (hr : 0 ≤ r) (f : Polynomial ℂ) (n : ℕ) :
    ‖f.coeff n‖ * r ^ n ≤ wnorm r f :=
  (summable_wnorm r f).le_tsum n fun m _ ↦ by positivity

private theorem wnorm_nonneg {r : ℝ} (hr : 0 ≤ r) (f : Polynomial ℂ) : 0 ≤ wnorm r f :=
  tsum_nonneg fun n ↦ by positivity

private theorem wnorm_mul_le {r : ℝ} (hr : 0 ≤ r) (f g : Polynomial ℂ) :
    wnorm r (f * g) ≤ wnorm r f * wnorm r g := by
  let a : ℕ → ℝ := fun n ↦ ‖f.coeff n‖ * r ^ n
  let b : ℕ → ℝ := fun n ↦ ‖g.coeff n‖ * r ^ n
  have ha : Summable fun n ↦ ‖a n‖ := by
    simpa [a, abs_of_nonneg, hr, pow_nonneg] using summable_wnorm r f
  have hb : Summable fun n ↦ ‖b n‖ := by
    simpa [b, abs_of_nonneg, hr, pow_nonneg] using summable_wnorm r g
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb
  change ∑' n, ‖(f * g).coeff n‖ * r ^ n ≤ (∑' n, a n) * ∑' n, b n
  rw [key]
  refine Summable.tsum_le_tsum (fun n ↦ ?_) (summable_wnorm r _)
    (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb).of_norm
  rw [Polynomial.coeff_mul]
  calc ‖∑ p ∈ Finset.antidiagonal n, f.coeff p.1 * g.coeff p.2‖ * r ^ n
      ≤ (∑ p ∈ Finset.antidiagonal n, ‖f.coeff p.1‖ * ‖g.coeff p.2‖) * r ^ n := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_mul_le _ _)
    _ = ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← Finset.mem_antidiagonal.1 hp, pow_add]
        ring

private theorem wnorm_one (r : ℝ) : wnorm r 1 = 1 := by
  rw [wnorm, tsum_eq_single 0 fun n hn ↦ by simp [Polynomial.coeff_one, hn]]
  simp

private theorem wnorm_prod_le {r : ℝ} (hr : 0 ≤ r) {J : Type*} (s : Finset J)
    (f : J → Polynomial ℂ) : wnorm r (∏ j ∈ s, f j) ≤ ∏ j ∈ s, wnorm r (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wnorm_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (wnorm_mul_le hr _ _).trans
      (mul_le_mul_of_nonneg_left ih (wnorm_nonneg hr _))

private theorem wnorm_multiset_prod_le {r : ℝ} (hr : 0 ≤ r) (s : Multiset (Polynomial ℂ)) :
    wnorm r s.prod ≤ (s.map (wnorm r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [wnorm_one]
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact (wnorm_mul_le hr _ _).trans (mul_le_mul_of_nonneg_left ih (wnorm_nonneg hr _))

private theorem wnorm_one_sub_C_mul_X_pow_le {r : ℝ} (hr : 0 ≤ r) (a : ℂ) (e : ℕ) :
    wnorm r (1 - Polynomial.C a * Polynomial.X ^ e) ≤ 1 + ‖a‖ * r ^ e := by
  have hs : Summable fun n ↦ (if n = 0 then 1 else 0) * r ^ n + (if n = e then ‖a‖ else 0) *
      r ^ n :=
    summable_of_ne_finset_zero (s := {0, e}) fun n hn ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [hn.1, hn.2]
  refine (Summable.tsum_le_tsum (fun n ↦ ?_) (summable_wnorm r _) hs).trans_eq ?_
  · rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow, ← add_mul]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    gcongr
    · split_ifs <;> simp
    · split_ifs <;> simp
  · rw [Summable.tsum_add (summable_of_ne_finset_zero (s := {0}) fun n hn ↦ by
        simp_all) (summable_of_ne_finset_zero (s := {e}) fun n hn ↦ by simp_all)]
    rw [tsum_eq_single 0 fun n hn ↦ by simp [hn], tsum_eq_single e fun n hn ↦ by simp [hn]]
    simp

/-- The weighted norm of a local polynomial with at most `d` roots of absolute value at most
`c ^ e`. -/
private theorem wnorm_eulerPoly_le {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) {M : Multiset ℂ} {e d : ℕ}
    (hM : ∀ a ∈ M, ‖a‖ ≤ c ^ e) (hd : Multiset.card M ≤ d) :
    wnorm r (eulerPoly M e) ≤ Real.exp (d * (c * r) ^ e) := by
  set b : ℝ := (c * r) ^ e
  have hb : 0 ≤ b := by positivity
  rw [eulerPoly, Polynomial.multiset_prod_comp, Multiset.map_map]
  refine (wnorm_multiset_prod_le hr _).trans ?_
  rw [Multiset.map_map]
  have hle : ∀ a ∈ M,
      wnorm r ((1 - Polynomial.C a * Polynomial.X).comp (Polynomial.X ^ e)) ≤ 1 + b := by
    intro a ha
    rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp]
    refine (wnorm_one_sub_C_mul_X_pow_le hr _ _).trans ?_
    gcongr
    calc ‖a‖ * r ^ e ≤ c ^ e * r ^ e := by gcongr; exact hM a ha
      _ = b := by simp only [b, mul_pow]
  calc _ ≤ (M.map fun _ ↦ 1 + b).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun a _ ↦ wnorm_nonneg hr _) fun a ha ↦ hle a ha
    _ = (1 + b) ^ Multiset.card M := by simp
    _ ≤ (1 + b) ^ d := pow_le_pow_right₀ (by linarith) hd
    _ ≤ Real.exp b ^ d := by
        gcongr
        linarith [Real.add_one_le_exp b]
    _ = Real.exp (d * b) := by rw [← Real.exp_nat_mul]

variable {J : Type*} {e : J → ℕ}

/-- The indices of degree at most `n`. -/
private noncomputable def lowDegree (hfin : ∀ n, {x | e x ≤ n}.Finite) (n : ℕ) : Finset J :=
  (hfin n).toFinset

private theorem mem_lowDegree {hfin : ∀ n, {x | e x ≤ n}.Finite} {n : ℕ} {x : J} :
    x ∈ lowDegree hfin n ↔ e x ≤ n := by
  simp [lowDegree]

private theorem X_pow_dvd_inv_eulerPoly_sub_one_of_notMem (he : ∀ x, e x ≠ 0)
    {hfin : ∀ n, {x | e x ≤ n}.Finite} (M : J → Multiset ℂ) {n : ℕ} {x : J}
    (hx : x ∉ lowDegree hfin n) :
    (X : ℂ⟦X⟧) ^ (n + 1) ∣ ((eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧)⁻¹ - 1 := by
  rw [mem_lowDegree, not_le] at hx
  exact (pow_dvd_pow X hx).trans (X_pow_dvd_inv_eulerPoly_sub_one (M x) (he x))

/-- The Euler product of the local polynomials has constant term `1`. -/
theorem constantCoeff_tprod_inv_eulerPoly (he : ∀ x, e x ≠ 0)
    (hfin : ∀ n, {x | e x ≤ n}.Finite) (M : J → Multiset ℂ) :
    constantCoeff (∏' x, ((eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧)⁻¹) = 1 := by
  have hS (m : ℕ) : ∀ x ∉ lowDegree hfin m,
      (X : ℂ⟦X⟧) ^ (m + 1) ∣ ((eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧)⁻¹ - 1 :=
    fun x hx ↦ X_pow_dvd_inv_eulerPoly_sub_one_of_notMem he M hx
  rw [← coeff_zero_eq_constantCoeff_apply, WithPiTopology.coeff_tprod_of_X_pow_dvd_sub_one
    (lowDegree hfin) hS _ (hS 0) le_rfl, coeff_zero_eq_constantCoeff_apply, map_prod]
  exact Finset.prod_eq_one fun x _ ↦ by
    rw [constantCoeff_inv, constantCoeff_eulerPoly _ (he x), inv_one]

/-- The coefficients of degree at most `n` of the inverse of the Euler product are those of the
finite product of the local polynomials at the points of degree at most `n`. -/
private theorem coeff_inv_tprod_inv_eulerPoly (he : ∀ x, e x ≠ 0)
    (hfin : ∀ n, {x | e x ≤ n}.Finite) (M : J → Multiset ℂ) (n : ℕ) :
    coeff n (∏' x, ((eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧)⁻¹)⁻¹ =
      (∏ x ∈ lowDegree hfin n, eulerPoly (M x) (e x)).coeff n := by
  set S := lowDegree hfin n
  set f : J → ℂ⟦X⟧ := fun x ↦ ((eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧)⁻¹
  set L := ∏' x, f x
  set F : ℂ⟦X⟧ := ∏ x ∈ S, f x
  have hS (m : ℕ) : ∀ x ∉ lowDegree hfin m, (X : ℂ⟦X⟧) ^ (m + 1) ∣ f x - 1 :=
    fun x hx ↦ X_pow_dvd_inv_eulerPoly_sub_one_of_notMem he M hx
  have hcoeff (k : ℕ) (hk : k ≤ n) : coeff k L = coeff k F :=
    WithPiTopology.coeff_tprod_of_X_pow_dvd_sub_one (lowDegree hfin) hS S (hS n) hk
  have hf0 (x : J) : constantCoeff (f x) = 1 := by
    simp only [f]
    rw [constantCoeff_inv, constantCoeff_eulerPoly _ (he x), inv_one]
  have hF0 : constantCoeff F = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun x _ ↦ hf0 x
  have hL0 : constantCoeff L = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hcoeff 0 (Nat.zero_le _),
      coeff_zero_eq_constantCoeff_apply, hF0]
  have hLF : X ^ (n + 1) ∣ L - F := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hcoeff m (Nat.lt_succ_iff.1 hm), sub_self]
  have hinv := X_pow_dvd_inv_sub_inv (by rw [hL0]; exact one_ne_zero)
    (by rw [hF0]; exact one_ne_zero) hLF
  have hFinv : F⁻¹ = ((∏ x ∈ S, eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by rw [hF0]; exact one_ne_zero),
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ ↦ by
      rw [Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.mul_inv_cancel _
        (by rw [constantCoeff_eulerPoly _ (he x)]; exact one_ne_zero)]
  rw [X_pow_dvd_iff] at hinv
  rw [← Polynomial.coeff_coe, ← hFinv, ← sub_eq_zero, ← map_sub]
  exact hinv n (Nat.lt_succ_self n)

/-- Step 1 of `proposition-weights-j-boundary-points--1`: the pole-free region of the open part.

Let the closed points of `J`, of degrees `e x ≥ 1`, number at most `A qⁿ` in degree `n`, and let
the local polynomial at `x` have at most `d` local roots, all of absolute value at most
`c ^ {e x}`. Then the inverse of the Euler product `∏_x P_x (T)⁻¹` converges on the disc of
radius `r` whenever `q c r < 1`. -/
theorem le_radius_inv_tprod_inv_eulerPoly (he : ∀ x, e x ≠ 0)
    (hfin : ∀ n, {x | e x ≤ n}.Finite) (M : J → Multiset ℂ) {c q A : ℝ} {d : ℕ} (hc : 0 ≤ c)
    (hq : 0 ≤ q) (hM : ∀ x, ∀ a ∈ M x, ‖a‖ ≤ c ^ e x) (hd : ∀ x, Multiset.card (M x) ≤ d)
    (hA : ∀ (s : Finset J) (n : ℕ), ((s.filter fun x ↦ e x = n).card : ℝ) ≤ A * q ^ n)
    {r : ℝ≥0} (hr : q * c * r < 1) :
    (r : ℝ≥0∞) ≤ (∏' x, ((eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧)⁻¹)⁻¹.radius := by
  classical
  set b : ℝ := c * r
  have hb : 0 ≤ b := by positivity
  have hqb : q * b < 1 := by rw [← mul_assoc]; exact hr
  have hA0 : 0 ≤ A := by
    have h := hA ∅ 0
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, pow_zero, mul_one] at h
    exact h
  set B : ℝ := A * ∑' n : ℕ, (q * b) ^ n
  have hgeom : Summable fun n : ℕ ↦ (q * b) ^ n :=
    summable_geometric_of_lt_one (by positivity) hqb
  -- the sum of `b ^ e_x` over a finite set of points is at most `B`
  have hsum (s : Finset J) : ∑ x ∈ s, b ^ e x ≤ B := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := e) (t := s.image e)
      fun x hx ↦ Finset.mem_image_of_mem _ hx]
    calc ∑ n ∈ s.image e, ∑ x ∈ s with e x = n, b ^ e x
        = ∑ n ∈ s.image e, ((s.filter fun x ↦ e x = n).card : ℝ) * b ^ n := by
          refine Finset.sum_congr rfl fun n _ ↦ ?_
          rw [Finset.sum_congr rfl fun x hx ↦ by rw [(Finset.mem_filter.1 hx).2],
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ s.image e, A * (q * b) ^ n := by
          refine Finset.sum_le_sum fun n _ ↦ ?_
          have h := mul_le_mul_of_nonneg_right (hA s n) (pow_nonneg hb n)
          rwa [mul_assoc, ← mul_pow] at h
      _ = A * ∑ n ∈ s.image e, (q * b) ^ n := by rw [Finset.mul_sum]
      _ ≤ B := mul_le_mul_of_nonneg_left
          (hgeom.sum_le_tsum _ fun n _ ↦ by positivity) hA0
  refine PowerSeries.le_radius_of_bound (Real.exp (d * B)) fun n ↦ ?_
  rw [coeff_inv_tprod_inv_eulerPoly he hfin M]
  refine (norm_coeff_mul_pow_le_wnorm (by positivity) _ n).trans ?_
  refine (wnorm_prod_le (by positivity) _ _).trans ?_
  calc ∏ x ∈ lowDegree hfin n, wnorm r (eulerPoly (M x) (e x))
      ≤ ∏ x ∈ lowDegree hfin n, Real.exp (d * b ^ e x) :=
        Finset.prod_le_prod₀ (fun x _ ↦ wnorm_nonneg (by positivity) _)
          fun x _ ↦ wnorm_eulerPoly_le (by positivity) hc (hM x) (hd x)
    _ = Real.exp (d * ∑ x ∈ lowDegree hfin n, b ^ e x) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (d * B) := by
        gcongr
        exact hsum _

/-- The analytic step of `proposition-weights-j-boundary-points--1` (Steps 1–3).

In the situation of `PowerSeries.le_radius_inv_tprod_inv_eulerPoly`, suppose that the Euler
product `L (T) = ∏_x P_x (T)⁻¹` satisfies `L (T) · ∏_{b ∈ S} (1 - b T) = P · B` for polynomials
`P` and `B`, where every `b ∈ S` has `|b| ≤ q c`. Then `B` has no zero in the disc `|T| < (q c)⁻¹`:
every zero `z` has `1 ≤ q c |z|`.

Indeed `B⁻¹ = (P / ∏ (1 - b T)) · L (T)⁻¹`, and both factors converge on that disc. -/
theorem one_le_mul_norm_of_tprod_mul_eq_mul (he : ∀ x, e x ≠ 0)
    (hfin : ∀ n, {x | e x ≤ n}.Finite) (M : J → Multiset ℂ) {c q A : ℝ} {d : ℕ} (hc : 0 ≤ c)
    (hq : 0 ≤ q) (hM : ∀ x, ∀ a ∈ M x, ‖a‖ ≤ c ^ e x) (hd : ∀ x, Multiset.card (M x) ≤ d)
    (hA : ∀ (s : Finset J) (n : ℕ), ((s.filter fun x ↦ e x = n).card : ℝ) ≤ A * q ^ n)
    {S : Multiset ℂ} (hS : ∀ b ∈ S, ‖b‖ ≤ q * c) {P B : Polynomial ℂ} (hB0 : B.coeff 0 ≠ 0)
    (hP : (∏' x, ((eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧)⁻¹) *
      (S.map fun b ↦ 1 - C b * X).prod = P * B)
    {z : ℂ} (hz : B.eval z = 0) :
    1 ≤ q * c * ‖z‖ := by
  set L := ∏' x, ((eulerPoly (M x) (e x) : Polynomial ℂ) : ℂ⟦X⟧)⁻¹
  set D : ℂ⟦X⟧ := (S.map fun b ↦ 1 - C b * X).prod
  have hD0 : constantCoeff D = 1 := by
    rw [map_multiset_prod, Multiset.map_map, Multiset.prod_eq_one fun a ha ↦ by
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 ha
      simp]
  have hL0 : constantCoeff L = 1 := constantCoeff_tprod_inv_eulerPoly he hfin M
  have hBcoe : constantCoeff (B : ℂ⟦X⟧) ≠ 0 := by
    rwa [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  -- `B⁻¹ = P D⁻¹ L⁻¹`
  have hBinv : (B : ℂ⟦X⟧)⁻¹ = ((P : ℂ⟦X⟧) * D⁻¹) * L⁻¹ := by
    have hLD : constantCoeff (L * D) ≠ 0 := by
      rw [map_mul, hL0, hD0, mul_one]
      exact one_ne_zero
    symm
    rw [PowerSeries.eq_inv_iff_mul_eq_one hBcoe]
    calc (P : ℂ⟦X⟧) * D⁻¹ * L⁻¹ * B = (P * B) * (D⁻¹ * L⁻¹) := by ring
      _ = (L * D) * (L * D)⁻¹ := by rw [← hP, PowerSeries.mul_inv_rev]
      _ = 1 := PowerSeries.mul_inv_cancel _ hLD
  by_contra! hlt
  -- a radius `r > ‖z‖` with `q c r < 1`
  obtain ⟨r, hzr, hr⟩ : ∃ r : ℝ≥0, ‖z‖ < r ∧ q * c * r < 1 := by
    rcases eq_or_lt_of_le (mul_nonneg hq hc) with h0 | hpos
    · refine ⟨⟨‖z‖ + 1, by positivity⟩, ?_, ?_⟩
      · change ‖z‖ < ‖z‖ + 1
        linarith
      · rw [← h0, zero_mul]
        exact one_pos
    · refine ⟨⟨(‖z‖ + (q * c)⁻¹) / 2, by positivity⟩, ?_, ?_⟩
      · change ‖z‖ < (‖z‖ + (q * c)⁻¹) / 2
        have : ‖z‖ < (q * c)⁻¹ := by
          rw [← one_div, lt_div_iff₀ hpos, mul_comm]
          exact hlt
        linarith
      · change q * c * ((‖z‖ + (q * c)⁻¹) / 2) < 1
        have h1 : q * c * ‖z‖ < 1 := hlt
        have h2 : q * c * (q * c)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
        nlinarith
  have hr' : ∀ b ∈ S, ‖b‖ * r < 1 := fun b hb ↦
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hS b hb) r.2) hr
  have h1 : (r : ℝ≥0∞) ≤ ((P : ℂ⟦X⟧) * D⁻¹).radius := PowerSeries.le_radius_coe_mul_inv_prod P S hr'
  have h2 : (r : ℝ≥0∞) ≤ L⁻¹.radius :=
    le_radius_inv_tprod_inv_eulerPoly he hfin M hc hq hM hd hA hr
  have h3 : (‖z‖₊ : ℝ≥0∞) < ((B : ℂ⟦X⟧)⁻¹).radius := by
    rw [hBinv]
    exact lt_of_lt_of_le (by exact_mod_cast hzr)
      ((le_min h1 h2).trans (PowerSeries.min_radius_le_radius_mul _ _))
  exact PowerSeries.eval_ne_zero_of_lt_radius_inv hB0 h3 hz

end Radius

end PowerSeries
