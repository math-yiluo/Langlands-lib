/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Restriction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Purity of a lisse sheaf extends over the missing points of a dense open

Let `𝒢` be a lisse Weil sheaf on a smooth geometrically connected curve `C₀` over `𝔽_q`, and
`U₀ ⊆ C₀` a nonempty open on which `𝒢` is punctually `ι`-pure of weight `w`. Then `𝒢` is
punctually `ι`-pure of weight `w` on all of `C₀` (the consequence in
`corollary-unramified-boundary-point--2`, and the second assertion of
`proposition-weights-j-boundary-points`).

The argument is the one of `proposition-weights-j-boundary-points--1`, for the lisse sheaf
`𝒢 = j_* j^* 𝒢` (`lemma-boundary-stalk--2`), whose boundary stalks are its own stalks. On an affine
neighbourhood `X'₀` of a closed point `s`, the Euler product of `𝒢`
(`theorem-trace-formula-euler-product--4`) splits into the Euler series over the closed points of
`X'₀ ∩ U₀` and the finitely many local factors at the points of `X'₀ \ U₀`:

`L (X'₀ ∩ U₀, 𝒢, T) · ι det (1 - F T ∣ H_c²) = P · ∏_{s ∈ X'₀ \ U₀} ι P_s (𝒢, T ^ e_s)`.

The inverse of the open part converges on the disc of radius `q ^ (-(w / 2 + 1))`
(`AlgebraicGeometry.WeilGroup.le_radius_inv_tprod_eulerFactor`), and so does
`P / ι det (1 - F T ∣ H_c²)`, the eigenvalues on `H_c² = V_{π₁}(-1)` being bounded through a
single closed point of `U₀`. So the local polynomials at the points of `X'₀ \ U₀` have no zero
in that disc (`AlgebraicGeometry.WeilGroup.le_norm_of_mul_eq_mul`), which bounds the weights there
by `w + 2`. Tensor squares sharpen the bound to `w`, and the dual gives the lower bound.

## Main statements

- `AlgebraicGeometry.WeilGroup.le_norm_of_mul_eq_mul`: the analytic step, for any identity
  `L (T, ℱ, T) · ι det (1 - F T ∣ H) = P · B` with `B` a polynomial.
- `AlgebraicGeometry.WeilGroup.frobeniusWeight_le_of_isAffine`: on an affine curve, weights at
  most `β` at the closed points of a cofinite set give weights at most `β` everywhere.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_forall_mem_range`: punctual purity on a
  nonempty open gives punctual purity on the whole curve.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped PowerSeries.WithPiTopology NNReal ENNReal

namespace AlgebraicGeometry.WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

/-- The eigenvalues of the geometric Frobenius on `H_c² (U, ℱ) = V_{π₁(U)} (-1)` are bounded by
`q ^ (β / 2 + 1)` as soon as `ℱ` has weights at most `β` at a single closed point `x`.

Since `π₁(U)` acts trivially on the coinvariants, the local Frobenius `F_x` of degree `e` acts on
them as `γ ^ e`. If `μ` is an eigenvalue of `q γ`, then `(μ / q) ^ e` is an eigenvalue of `F_x` on
the quotient `V_{π₁(U)}` of `V`, hence of `F_x` on `V`, so it has weight at most `β`. -/
theorem norm_le_of_hasEigenvalue_compactTopFrobenius_of_forall (x : C.finitePoints) {β : ℝ}
    (hw : ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β)
    {μ : PadicAlgCl l} (hμ : (W.compactTopFrobenius l ρ).HasEigenvalue μ) :
    ‖ι μ‖ ≤ (Nat.card K : ℝ) ^ (β / 2 + 1) := by
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq : 1 < q := by
    have := (Finite.one_lt_card_iff_nontrivial (α := K)).2 inferInstance
    rw [hqdef]
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqK : (Nat.card K : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  set G := W.geometric
  set Q := ρ.toCoinvariants G
  set T := Q W.frobeniusLift
  set c := μ / (Nat.card K : PadicAlgCl l)
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simp only [map_zero, norm_zero]
    positivity
  -- `c` is an eigenvalue of `γ` on the coinvariants
  have hc : Module.End.HasEigenvalue T c := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    have h := hv.apply_eq_smul
    rw [compactTopFrobenius, LinearMap.smul_apply] at h
    calc T v = (Nat.card K : PadicAlgCl l)⁻¹ • ((Nat.card K : PadicAlgCl l) • T v) := by
          rw [smul_smul, inv_mul_cancel₀ hqK, one_smul]
      _ = c • v := by rw [h, smul_smul, inv_mul_eq_div]
  -- the local Frobenius at `x` acts on the coinvariants as `γ ^ e`
  set e := p.degreeOver x.1
  have he : e ≠ 0 := p.degreeOver_ne_zero x.2
  have htriv (g : W.carrier) (hg : g ∈ G) : Q g = 1 :=
    (inferInstance : Representation.IsTrivial (Q.comp G.subtype)).out ⟨g, hg⟩
  have hn : W.frobenius x * (W.frobeniusLift ^ e)⁻¹ ∈ G := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, W.deg_frobenius, W.deg_frobeniusLift,
      ← ofAdd_nsmul, nsmul_one, mul_inv_eq_one]
  have hQx : Q (W.frobenius x) = T ^ e := by
    rw [show W.frobenius x = (W.frobenius x * (W.frobeniusLift ^ e)⁻¹) * W.frobeniusLift ^ e
      by group, map_mul, htriv _ hn, one_mul, map_pow]
  have hce : Module.End.HasEigenvalue (Q (W.frobenius x)) (c ^ e) := by
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw.2⟩
    rw [Module.End.mem_eigenspace_iff, hQx]
    exact hw.pow_apply e
  -- hence `c ^ e` is a local eigenvalue of `ρ` at `x`
  have hρx : Module.End.HasEigenvalue (ρ (W.frobenius x)) (c ^ e) :=
    Module.End.hasEigenvalue_of_comp_eq_comp (ρ (W.frobenius x)) (Q (W.frobenius x))
      (Representation.Coinvariants.mk _) (Representation.Coinvariants.mk_surjective _)
      (LinearMap.ext fun v ↦ rfl) hce
  have hmem : c ^ e ∈ W.localEigenvalues l ρ x := by
    rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hρx
  have hc0 : c ≠ 0 := div_ne_zero hμ0 hqK
  have hwt := hw _ hmem
  rw [frobeniusWeight_le_iff ι (C.one_lt_pointNorm x.2) ((map_ne_zero ι).2 (pow_ne_zero _ hc0)),
    Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2] at hwt
  -- `|ι c| ≤ q ^ (β / 2)`
  have hcle : ‖ι c‖ ≤ q ^ (β / 2) := by
    have h1 : ‖ι c‖ ^ (2 * e) ≤ (q ^ (β / 2)) ^ (2 * e) := by
      calc ‖ι c‖ ^ (2 * e) = ‖ι (c ^ e)‖ ^ 2 := by rw [map_pow, norm_pow, ← pow_mul, mul_comm]
        _ ≤ _ := hwt
        _ = (q ^ (β / 2)) ^ (2 * e) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast (q ^ (β / 2)), ← Real.rpow_mul hq0.le,
            ← Real.rpow_natCast q e, ← Real.rpow_mul hq0.le]
          push_cast
          ring_nf
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity)
      (mul_ne_zero two_ne_zero he)).1 h1
  have hμc : ‖ι μ‖ = q * ‖ι c‖ := by
    rw [show μ = (Nat.card K : PadicAlgCl l) * c by simp only [c]; field_simp, map_mul, norm_mul,
      map_natCast, Complex.norm_natCast]
  rw [hμc, Real.rpow_add hq0, Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_right hcle hq0.le

variable {W l ρ ι}

/-- The analytic step of `proposition-weights-j-boundary-points--1` (Steps 1–3).

Let `T` be a set of closed points with at most `A q ^ e` points of degree `e`, at which `ℱ` has
weights at most `β`, and suppose that the Euler series of `ℱ` over `T` satisfies
`L (T, ℱ, T) · ∏_{c ∈ S} (1 - c T) = P · B` for polynomials `P` and `B`, where every `c ∈ S`
has `|c| ≤ q ^ (β / 2 + 1)`. Then `B` has no zero in the disc of radius `R = q ^ (-(β / 2 + 1))`.

Indeed `B⁻¹ = (P / ∏ (1 - c T)) · L (T, ℱ, T)⁻¹`, and both factors converge on that disc
(`PowerSeries.le_radius_coe_mul_inv_prod`,
`AlgebraicGeometry.WeilGroup.le_radius_inv_tprod_eulerFactor`). -/
theorem le_norm_of_mul_eq_mul (T : Set C.finitePoints) {β : ℝ}
    (hw : ∀ x ∈ T, ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β)
    {A : ℝ} (hA : ∀ (s : Finset T) (e : ℕ),
      ((s.filter fun x ↦ p.degreeOver x.1.1 = e).card : ℝ) ≤ A * (Nat.card K : ℝ) ^ e)
    {S : Multiset ℂ} (hS : ∀ c ∈ S, ‖c‖ ≤ (Nat.card K : ℝ) ^ (β / 2 + 1))
    {P B : Polynomial ℂ} (hB0 : B.coeff 0 ≠ 0)
    (hP : (∏' x : T, W.eulerFactor l ρ ι x.1) *
      (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod = P * B)
    {z : ℂ} (hz : B.eval z = 0) :
    (Nat.card K : ℝ) ^ (-(β / 2 + 1)) ≤ ‖z‖ := by
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; exact_mod_cast Nat.card_pos (α := K)
  set R : ℝ := q ^ (-(β / 2 + 1))
  have hR : 0 < R := Real.rpow_pos_of_pos hq0 _
  have hRq : q ^ (β / 2 + 1) * R = 1 := by
    rw [← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  set L := ∏' x : T, W.eulerFactor l ρ ι x.1
  set Dser : PowerSeries ℂ := (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod
  have hDser0 : PowerSeries.constantCoeff Dser = 1 := by
    rw [map_multiset_prod, Multiset.map_map, Multiset.prod_eq_one fun a ha ↦ by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
      simp]
  have hL0 : PowerSeries.constantCoeff L = 1 := W.constantCoeff_tprod_eulerFactor l ρ ι T
  have hBcoe : PowerSeries.constantCoeff (B : PowerSeries ℂ) ≠ 0 := by
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  -- `B⁻¹ = P D⁻¹ L⁻¹`
  have hBinv : (B : PowerSeries ℂ)⁻¹ = ((P : PowerSeries ℂ) * Dser⁻¹) * L⁻¹ := by
    have hLD : PowerSeries.constantCoeff (L * Dser) ≠ 0 := by
      rw [map_mul, hL0, hDser0, mul_one]
      exact one_ne_zero
    symm
    rw [PowerSeries.eq_inv_iff_mul_eq_one hBcoe]
    calc (P : PowerSeries ℂ) * Dser⁻¹ * L⁻¹ * B = (P * B) * (Dser⁻¹ * L⁻¹) := by ring
      _ = (L * Dser) * (L * Dser)⁻¹ := by rw [← hP, PowerSeries.mul_inv_rev]
      _ = 1 := PowerSeries.mul_inv_cancel _ hLD
  by_contra! hlt
  set r : NNReal := ⟨(‖z‖ + R) / 2, by positivity⟩
  have hzr : ‖z‖ < r := by change ‖z‖ < (‖z‖ + R) / 2; linarith
  have hrR : (r : ℝ) < R := by change (‖z‖ + R) / 2 < R; linarith
  have hr : ∀ c ∈ S, ‖c‖ * r < 1 := fun c hc ↦ by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · calc ‖c‖ * r < ‖c‖ * R := mul_lt_mul_of_pos_left hrR (norm_pos_iff.2 hc0)
        _ ≤ q ^ (β / 2 + 1) * R := mul_le_mul_of_nonneg_right (hS c hc) hR.le
        _ = 1 := hRq
  have h1 : (r : ENNReal) ≤ ((P : PowerSeries ℂ) * Dser⁻¹).radius :=
    PowerSeries.le_radius_coe_mul_inv_prod P S hr
  have h2 : (r : ENNReal) ≤ L⁻¹.radius :=
    W.le_radius_inv_tprod_eulerFactor l ρ ι T hw hA (by
      calc q ^ (β / 2 + 1) * r < q ^ (β / 2 + 1) * R :=
            mul_lt_mul_of_pos_left hrR (by positivity)
        _ = 1 := hRq)
  have h3 : (‖z‖₊ : ENNReal) < ((B : PowerSeries ℂ)⁻¹).radius := by
    rw [hBinv]
    exact lt_of_lt_of_le (by exact_mod_cast hzr)
      ((le_min h1 h2).trans (PowerSeries.min_radius_le_radius_mul _ _))
  exact PowerSeries.eval_ne_zero_of_lt_radius_inv hB0 h3 hz

omit [Finite K] in
/-- A zero `z` of `1 - ι α T ^ e` outside the disc of radius `q ^ (-(β / 2 + 1))` bounds the weight
of `α` relative to `q ^ e` by `β + 2`. -/
theorem frobeniusWeight_le_add_two_of_le_norm [Finite K] {α : PadicAlgCl l} (hα0 : ι α ≠ 0)
    {e : ℕ} (he : e ≠ 0) {z : ℂ} (hz : z ^ e = (ι α)⁻¹) {β : ℝ}
    (hzR : (Nat.card K : ℝ) ^ (-(β / 2 + 1)) ≤ ‖z‖) :
    frobeniusWeight ι (Nat.card K ^ e) α ≤ β + 2 := by
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq : 1 < q := by
    have := (Finite.one_lt_card_iff_nontrivial (α := K)).2 inferInstance
    rw [hqdef]
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq
  set R : ℝ := q ^ (-(β / 2 + 1))
  have hR : 0 < R := Real.rpow_pos_of_pos hq0 _
  have hnorm : ‖ι α‖ ≤ q ^ ((e : ℝ) * (β / 2 + 1)) := by
    have hze : ‖z‖ ^ e = ‖ι α‖⁻¹ := by rw [← norm_pow, hz, norm_inv]
    have hRe : R ^ e ≤ ‖ι α‖⁻¹ := hze ▸ pow_le_pow_left₀ hR.le hzR e
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le] at hRe
    have := (le_inv_comm₀ (by positivity) (norm_pos_iff.2 hα0)).1 hRe
    rwa [← Real.rpow_neg hq0.le, neg_mul, neg_neg, mul_comm] at this
  rw [frobeniusWeight, Nat.cast_pow, Real.log_pow,
    div_le_iff₀ (mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)) (Real.log_pos hq))]
  have := Real.log_le_log (norm_pos_iff.2 hα0) hnorm
  rw [Real.log_rpow hq0] at this
  change 2 * Real.log ‖ι α‖ ≤ (β + 2) * (e * Real.log q)
  nlinarith

variable (W l ρ ι)

/-- The local polynomial `ι P_x (ℱ, T ^ e_x)` is `1` modulo `T ^ e_x`. -/
theorem X_pow_dvd_coe_localPolynomial_sub_one (x : C.finitePoints) :
    (PowerSeries.X : PowerSeries ℂ) ^ p.degreeOver x.1 ∣
      ((((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ p.degreeOver x.1) :
        Polynomial ℂ) : PowerSeries ℂ) - 1 := by
  have hP : (Polynomial.X : Polynomial ℂ) ∣ (W.localPolynomial l ρ x).map ι - 1 := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_zero_eq_eval_zero,
      eval_zero_map_localPolynomial, Polynomial.coeff_one_zero, sub_self]
  obtain ⟨R, hR⟩ := hP
  have hQ : (Polynomial.X : Polynomial ℂ) ^ p.degreeOver x.1 ∣
      ((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ p.degreeOver x.1) - 1 :=
    ⟨R.comp (Polynomial.X ^ p.degreeOver x.1), by
      rw [← Polynomial.one_comp (p := Polynomial.X ^ _), ← Polynomial.sub_comp, hR,
        Polynomial.mul_comp, Polynomial.X_comp]⟩
  have hQ' := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) hQ
  simpa only [map_pow, map_sub, map_one, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X] using hQ'

/-- The Euler product over any set of closed points converges. -/
theorem multipliable_eulerFactor_subtype (T : Set C.finitePoints) :
    Multipliable fun x : T ↦ W.eulerFactor l ρ ι x.1 :=
  PowerSeries.WithPiTopology.multipliable_inv_of_X_pow_dvd_sub_one
    (e := fun x : T ↦ p.degreeOver x.1.1) (fun x ↦ p.degreeOver_ne_zero x.1.2)
    (fun x ↦ X_pow_dvd_coe_localPolynomial_sub_one W l ρ ι x.1)
    (fun n ↦ (p.finite_setOf_degreeOver_le n).preimage Subtype.val_injective.injOn)

/-- The Euler series splits into the Euler product over a set `T` of closed points with finite
complement and the finitely many local factors at the points outside `T`. -/
theorem eulerSeries_eq_tprod_mul_prod {T : Set C.finitePoints} (hT : Tᶜ.Finite) :
    W.eulerSeries l ρ ι =
      (∏' x : T, W.eulerFactor l ρ ι x.1) * ∏ x ∈ hT.toFinset, W.eulerFactor l ρ ι x := by
  have : Finite ↥Tᶜ := hT.to_subtype
  rw [eulerSeries, ← (W.multipliable_eulerFactor_subtype l ρ ι T).tprod_mul_tprod_compl
    (Multipliable.of_finite), ← Finset.tprod_subtype']
  congr 1
  exact tprod_congr_set_coe _ hT.coe_toFinset.symm

/-- Steps 0–3 of `proposition-weights-j-boundary-points--1` for a lisse sheaf on an affine curve.

Let `C₀` be a smooth geometrically connected affine curve, `ℱ` lisse on `C₀` and `T` a set of
closed points with finite complement, containing some point `x₀`, at which `ℱ` has weights at
most `β`. Then every local eigenvalue of `ℱ`, at any closed point, has weight at most `β + 2`.

By the Euler product of `ℱ` (`theorem-trace-formula-euler-product--4`), split into the Euler product
over `T` and the local factors at the points outside `T`
(`AlgebraicGeometry.WeilGroup.eulerSeries_eq_tprod_mul_prod`), the product `B` of the local
polynomials outside `T` satisfies `L (T, ℱ, T) · ι det (1 - F T ∣ H_c²) = P · B`. The eigenvalues
on `H_c²` are bounded through the point `x₀`
(`AlgebraicGeometry.WeilGroup.norm_le_of_hasEigenvalue_compactTopFrobenius_of_forall`), so `B`
has no zero in the disc of radius `q ^ (-(β / 2 + 1))`
(`AlgebraicGeometry.WeilGroup.le_norm_of_mul_eq_mul`). -/
theorem frobeniusWeight_le_add_two_of_isAffine [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] (hρ : W.IsLisse l ρ)
    {T : Set C.finitePoints} (hT : Tᶜ.Finite) {x₀ : C.finitePoints} (hx₀ : x₀ ∈ T) {β : ℝ}
    (hw : ∀ x ∈ T, ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β)
    (s : C.finitePoints) {α : PadicAlgCl l} (hα : α ∈ W.localEigenvalues l ρ s) :
    frobeniusWeight ι (C.pointNorm s.1) α ≤ β + 2 := by
  classical
  by_cases hs : s ∈ T
  · linarith [hw s hs α hα]
  -- the Euler product identity
  obtain ⟨P, hP⟩ := exists_eulerSeries_mul_eq_coe ρ ι hρ
  obtain ⟨A, hA⟩ := p.exists_card_filter_degreeOver_le (IsCurve.krullDim_le_one p)
  set lp : C.finitePoints → Polynomial ℂ := fun x ↦
    ((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ p.degreeOver x.1)
  set B : Polynomial ℂ := ∏ x ∈ hT.toFinset, lp x
  set S := (W.compactTopFrobenius l ρ).charpoly.roots.map ι
  have hS : ∀ c ∈ S, ‖c‖ ≤ (Nat.card K : ℝ) ^ (β / 2 + 1) := by
    intro c hc
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hc
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hμ
    exact W.norm_le_of_hasEigenvalue_compactTopFrobenius_of_forall l ρ ι x₀ (hw x₀ hx₀) hμ
  have hDser : (((W.compactTopFrobenius l ρ).charpolyRev.map ι : Polynomial ℂ) :
      PowerSeries ℂ) = (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod := by
    rw [LinearMap.charpolyRev_eq_prod_roots, Polynomial.map_multiset_prod_one_sub_C_mul_X,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun c _ ↦ by simp)
  have hlp0 (x : C.finitePoints) : PowerSeries.constantCoeff ((lp x : Polynomial ℂ) :
      PowerSeries ℂ) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_pow,
      Polynomial.eval_X, zero_pow (p.degreeOver_ne_zero x.2), eval_zero_map_localPolynomial]
    exact one_ne_zero
  have hFB : (∏ x ∈ hT.toFinset, W.eulerFactor l ρ ι x) * (B : PowerSeries ℂ) = 1 := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ ↦ PowerSeries.inv_mul_cancel _ (hlp0 x)
  have hP' : (∏' x : T, W.eulerFactor l ρ ι x.1) *
      (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod = P * B := by
    rw [← hDser, ← hP, W.eulerSeries_eq_tprod_mul_prod l ρ ι hT]
    linear_combination -(∏' x : T, W.eulerFactor l ρ ι x.1) *
      (((W.compactTopFrobenius l ρ).charpolyRev.map ι : Polynomial ℂ) : PowerSeries ℂ) * hFB
  have hB0 : B.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun x _ ↦ ?_
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
      zero_pow (p.degreeOver_ne_zero x.2), eval_zero_map_localPolynomial]
    exact one_ne_zero
  -- the zero `z` of the local polynomial at `s`
  set e := p.degreeOver s.1
  have he : e ≠ 0 := p.degreeOver_ne_zero s.2
  have hα0 : ι α ≠ 0 :=
    (map_ne_zero ι).2 fun h ↦ zero_notMem_localEigenvalues (ρ := ρ) s (h ▸ hα)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι α)⁻¹ (Nat.pos_of_ne_zero he)
  have hBz : B.eval z = 0 := by
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero (i := s) (hT.mem_toFinset.2 hs) ?_
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, hz, map_localPolynomial,
      Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨1 - Polynomial.C (ι α) * Polynomial.X,
      Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem ι hα), ?_⟩)
    simp [hα0]
  have hzR := le_norm_of_mul_eq_mul T hw (hA T) hS hB0 hP' hBz
  rw [Scheme.Hom.pointNorm_eq_pow_degreeOver p s.2]
  exact frobeniusWeight_le_add_two_of_le_norm hα0 he hz hzR

/-- Step 4 of `proposition-weights-j-boundary-points--1` for a lisse sheaf on an affine curve:
sharpening by tensor powers. Applying
`AlgebraicGeometry.WeilGroup.frobeniusWeight_le_add_two_of_isAffine` to the iterated tensor squares
`ℱ ^ ⊗ 2 ^ k`, of weights at most `2 ^ k β` on `T` and with the local eigenvalue `α ^ (2 ^ k)`,
gives `wt (α) ≤ β + 2 / 2 ^ k`. -/
theorem frobeniusWeight_le_add_div_two_pow_of_isAffine [IsAffine C]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [Fact (ringChar K ≠ l)] (k : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
      [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V),
      W.IsLisse l ρ → ∀ {T : Set C.finitePoints}, Tᶜ.Finite → ∀ {x₀ : C.finitePoints}, x₀ ∈ T →
      ∀ {β : ℝ}, (∀ x ∈ T, ∀ α ∈ W.localEigenvalues l ρ x,
        frobeniusWeight ι (C.pointNorm x.1) α ≤ β) →
      ∀ (s : C.finitePoints) {α : PadicAlgCl l}, α ∈ W.localEigenvalues l ρ s →
        frobeniusWeight ι (C.pointNorm s.1) α ≤ β + 2 / 2 ^ k := by
  induction k with
  | zero =>
    intro V _ _ _ ρ hρ T hT x₀ hx₀ β hw s α hα
    simpa using W.frobeniusWeight_le_add_two_of_isAffine l ρ ι hρ hT hx₀ hw s hα
  | succ k ih =>
    intro V _ _ _ ρ hρ T hT x₀ hx₀ β hw s α hα
    have hw2 : ∀ x ∈ T, ∀ γ ∈ W.localEigenvalues l (ρ.tprod ρ) x,
        frobeniusWeight ι (C.pointNorm x.1) γ ≤ 2 * β := by
      intro x hx γ hγ
      rw [localEigenvalues_tprod] at hγ
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Multiset.mem_map.1 hγ
      rw [Multiset.mem_product] at hab
      rw [frobeniusWeight_mul ι _ (fun h ↦ zero_notMem_localEigenvalues x (h ▸ hab.1))
        (fun h ↦ zero_notMem_localEigenvalues x (h ▸ hab.2))]
      linarith [hw x hx a hab.1, hw x hx b hab.2]
    have h := ih (ρ.tprod ρ) (hρ.tprod hρ) hT hx₀ hw2 s (sq_mem_localEigenvalues_tprod_self hα)
    rw [frobeniusWeight_pow] at h
    have h2 : (2 : ℝ) / 2 ^ (k + 1) = 2 / 2 ^ k / 2 := by rw [pow_succ]; ring
    rw [h2]
    push_cast at h
    linarith

/-- `proposition-weights-j-boundary-points--1` for a lisse sheaf on an affine curve: if `ℱ` is lisse
on a smooth geometrically connected affine curve and has weights at most `β` at the closed points of
a nonempty set `T` with finite complement, then it has weights at most `β` everywhere. -/
theorem frobeniusWeight_le_of_isAffine [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] (hρ : W.IsLisse l ρ)
    {T : Set C.finitePoints} (hT : Tᶜ.Finite) {x₀ : C.finitePoints} (hx₀ : x₀ ∈ T) {β : ℝ}
    (hw : ∀ x ∈ T, ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β) :
    W.HasWeightsAtMost l ρ ι β := by
  intro s α hα
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε) one_half_lt_one
  have h := W.frobeniusWeight_le_add_div_two_pow_of_isAffine l ι k ρ hρ hT hx₀ hw s hα
  have hk' : (2 : ℝ) / 2 ^ k < ε := by
    rw [one_div_pow] at hk
    have : (2 : ℝ) / 2 ^ k = 2 * (1 / 2 ^ k) := by ring
    rw [this]
    linarith
  linarith

variable {W l ρ}

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- If `α` is a local eigenvalue of `ℱ` at `x`, then `α⁻¹` is a local eigenvalue of `ℱ ^ ∨`. -/
theorem inv_mem_localEigenvalues_dual [FiniteDimensional (PadicAlgCl l) V] {x : C.finitePoints}
    {α : PadicAlgCl l} (hα : α ∈ W.localEigenvalues l ρ x) :
    α⁻¹ ∈ W.localEigenvalues l ρ.dual x := by
  rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα ⊢
  rw [Representation.hasEigenvalue_dual_iff]
  exact ρ.hasEigenvalue_inv hα

/-- If `α` is a local eigenvalue of `ℱ ^ ∨` at `x`, then `α⁻¹` is a local eigenvalue of `ℱ`. -/
theorem inv_mem_localEigenvalues_of_mem_dual {x : C.finitePoints} {α : PadicAlgCl l}
    (hα : α ∈ W.localEigenvalues l ρ.dual x) : α⁻¹ ∈ W.localEigenvalues l ρ x := by
  rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα ⊢
  rw [Representation.hasEigenvalue_dual_iff] at hα
  simpa using ρ.hasEigenvalue_inv hα

variable (W l ρ)

/-- Weights at most `β` on a nonempty open `U₀` of a smooth geometrically connected curve `C₀`
give weights at most `β` on all of `C₀`, for a lisse sheaf on `C₀`.

Fix a closed point `x` and an affine open neighbourhood `X'₀` of it, a smooth geometrically
connected affine curve with a restriction of Weil groups `W(X'₀) → W(C₀)`
(`AlgebraicGeometry.WeilGroup.Restriction.exists_weilGroup`). The closed points of `X'₀` in `U₀`
form a nonempty set with finite complement, the boundary `C₀ \ U₀` being finite, so the affine case
(`AlgebraicGeometry.WeilGroup.frobeniusWeight_le_of_isAffine`) applies to the restriction of `ℱ`
to `X'₀`, whose local eigenvalues at `x` are those of `ℱ`. -/
theorem hasWeightsAtMost_of_forall_mem_range [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] {U : Scheme.{u}} (j : U ⟶ C)
    [IsOpenImmersion j] [Nonempty U] (hρ : W.IsLisse l ρ) {β : ℝ}
    (hw : ∀ x : C.finitePoints, x.1 ∈ Set.range j.base → ∀ α ∈ W.localEigenvalues l ρ x,
      frobeniusWeight ι (C.pointNorm x.1) α ≤ β) :
    W.HasWeightsAtMost l ρ ι β := by
  intro x α hα
  have := SmoothOfRelativeDimension.smooth 1 p
  have := W.connectedSpace
  obtain ⟨X', hX', hxX', -⟩ := exists_isAffineOpen_mem_and_subset (x := x.1) (U := ⊤) trivial
  have : IsAffine X' := hX'
  have : Nonempty X' := ⟨⟨x.1, hxX'⟩⟩
  have : IsCurve (X'.ι ≫ p) := isCurve_comp_of_isAffine X'.ι
  have : SmoothOfRelativeDimension 1 (X'.ι ≫ p) := by
    simpa using smoothOfRelativeDimension_comp (n := 0) (m := 1) X'.ι p
  have : GeometricallyConnected (X'.ι ≫ p) := geometricallyConnected_comp X'.ι
  obtain ⟨W', ⟨R⟩⟩ := Restriction.exists_weilGroup W X'.ι rfl
  set T : Set X'.toScheme.finitePoints := {y | (X'.ι.mapFinitePoints y).1 ∈ Set.range j.base}
  -- the points of `X'₀` outside `U₀` are boundary points of `U₀`
  have hT : Tᶜ.Finite := by
    refine ((finite_boundary (p := p) j).preimage
      (f := fun y : X'.toScheme.finitePoints ↦ X'.ι.base y.1) fun y _ y' _ h ↦ ?_).subset
      fun y hy ↦ hy
    exact Subtype.ext (X'.ι.isOpenEmbedding.injective h)
  -- a closed point of `X'₀` in `U₀`
  obtain ⟨x₀, hx₀⟩ : T.Nonempty := by
    have := irreducibleSpace_of_smooth (p := p)
    have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
    have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
    have : IsNoetherian C := {}
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    obtain ⟨y, hyX', hyU⟩ := nonempty_preirreducible_inter X'.isOpen j.opensRange.isOpen
      ⟨x.1, hxX'⟩ ⟨j.base u, u, rfl⟩
    set V := X' ⊓ j.opensRange
    have : Nonempty V := ⟨⟨y, hyX', hyU⟩⟩
    obtain ⟨v, hv⟩ := (V.ι ≫ p).exists_mem_finitePoints
    have hvC := (Scheme.Hom.mem_finitePoints_iff_of_isIso V.ι v).2 hv
    have hvX' : V.ι.base v ∈ X' := v.2.1
    refine ⟨⟨⟨V.ι.base v, hvX'⟩, (Scheme.Hom.mem_finitePoints_iff_of_isIso X'.ι _).1 hvC⟩, ?_⟩
    exact v.2.2
  -- weights at the points of `T`
  have hw' : ∀ y ∈ T, ∀ γ ∈ W'.localEigenvalues l (ρ.comp R.restrict) y,
      frobeniusWeight ι (X'.toScheme.pointNorm y.1) γ ≤ β := by
    intro y hy γ hγ
    rw [R.localEigenvalues_comp] at hγ
    rw [← X'.ι.pointNorm_mapFinitePoints]
    exact hw _ hy γ hγ
  have hy : (⟨x.1, hxX'⟩ : X') ∈ X'.toScheme.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso X'.ι _).1 x.2
  have hxy : X'.ι.mapFinitePoints ⟨_, hy⟩ = x := Subtype.ext rfl
  rw [← hxy] at hα ⊢
  rw [← R.localEigenvalues_comp] at hα
  rw [X'.ι.pointNorm_mapFinitePoints]
  exact frobeniusWeight_le_of_isAffine W' l (ρ.comp R.restrict) ι (R.isLisse_comp l hρ) hT hx₀
    hw' _ α hα

/-- Blueprint `corollary-unramified-boundary-point--2`: Purity at an unramified boundary point, the
consequence. Also the second assertion of `proposition-weights-j-boundary-points`.

A lisse Weil sheaf `𝒢` on a smooth geometrically connected curve `C₀` which is punctually
`ι`-pure of weight `w` at the closed points of a nonempty open `U₀` is punctually `ι`-pure of
weight `w` on all of `C₀`: the weights are at most `w`
(`AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_forall_mem_range`), and so are those of the
dual `𝒢 ^ ∨`, which is pure of weight `-w` on `U₀`, whose local eigenvalues are the inverses of
those of `𝒢`. -/
theorem isPunctuallyPure_of_forall_mem_range [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] {U : Scheme.{u}} (j : U ⟶ C)
    [IsOpenImmersion j] [Nonempty U] (hρ : W.IsLisse l ρ) {w : ℝ}
    (hpure : ∀ x : C.finitePoints, x.1 ∈ Set.range j.base → ∀ α ∈ W.localEigenvalues l ρ x,
      frobeniusWeight ι (C.pointNorm x.1) α = w) :
    W.IsPunctuallyPure l ρ ι w := by
  have hup := W.hasWeightsAtMost_of_forall_mem_range l ρ ι j hρ fun x hx α hα ↦
    (hpure x hx α hα).le
  have hdown := W.hasWeightsAtMost_of_forall_mem_range l ρ.dual ι j hρ.dual (β := -w)
    fun x hx α hα ↦ by
      have h := hpure x hx _ (inv_mem_localEigenvalues_of_mem_dual hα)
      rw [frobeniusWeight_inv] at h
      linarith
  intro x α hα
  have h1 := hup x α hα
  have h2 := hdown x _ (inv_mem_localEigenvalues_dual hα)
  rw [frobeniusWeight_inv] at h2
  linarith

end AlgebraicGeometry.WeilGroup
