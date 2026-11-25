/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin
public import WeilConjectures.PointCountBound

/-!
# Semi-continuity of weights at the boundary of an open subcurve

Let `j : U₀ ↪ C₀` be a nonempty open of a smooth geometrically connected curve over `𝔽_q`, with
a boundary datum, and let `ℱ` be a lisse Weil sheaf on `U₀` with punctual weights at most `β`.
This file proves that the middle extension `j_* ℱ` has punctual weights at most `β` at every
boundary point `s`: every eigenvalue `α` of the residue Frobenius `F_s` on the boundary stalk
`V ^ (I_s)` satisfies `|ι α| ^ 2 ≤ q_s ^ β` (`proposition-weights-j-boundary-points--1`).

The argument is analytic. On an affine neighbourhood `X'₀` of `s`, with `U'₀ = U₀ ∩ X'₀`:

* the inverse of the Euler series `L (U'₀, ℱ, T)` has radius of convergence at least
  `R = q ^ (-(β / 2 + 1))`, because the closed points of `U'₀` of degree `e` number at most
  `A q ^ e` (`lemma-point-count-bound--1`), so that the coefficients of the inverse are
  dominated by those of `∏_x (1 + q_x ^ (β / 2) T ^ e_x) ^ r`;
* the eigenvalues of the geometric Frobenius on `H_c² = V_{π₁(U)} (-1)`
(`lemma-degree-zero-top-cohomology--2`)
  have absolute value at most `q ^ (β / 2 + 1)`;
* the Euler product identity for `j_* ℱ` (`proposition-weights-j-boundary-points`), the
  Grothendieck–Lefschetz trace formula, then forces the boundary polynomials
  `det (1 - F_s T ^ e_s ∣ V ^ (I_s))` to have no zero in the disc `|T| < R`,

which gives `|ι α| ≤ q_s ^ (β / 2 + 1)`. Applying this to the tensor powers `ℱ ^ ⊗ 2 ^ k`, whose
boundary stalks contain `v ^ ⊗ 2 ^ k` for an eigenvector `v`, sharpens the bound to `β`.

## Implementation notes

The cohomology `H_c² (U, ℱ)` of a Weil representation is not available; as in
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin`, the coinvariant Tate twist
`V_{π₁(U)} (-1)` is used in its place (`AlgebraicGeometry.WeilGroup.compactTopFrobenius`).

The Euler-product form of the trace formula for middle extensions is the hypothesis
`AlgebraicGeometry.BoundaryDatum.HasMiddleExtensionEulerProduct` of the main results: the
Grothendieck–Lefschetz trace formula is not available, and the identity is not a consequence of
the fields of a `AlgebraicGeometry.BoundaryDatum`, which pin the inertia groups down only through
the closed normal subgroup they generate (`AlgebraicGeometry.BoundaryDatum.ker_restrict_eq`).

## Main definitions

- `AlgebraicGeometry.BoundaryDatum.boundaryPolynomial`: `ι det (1 - F_s T ^ e_s ∣ V ^ (I_s))`.
- `AlgebraicGeometry.BoundaryDatum.HasMiddleExtensionEulerProduct`: the Euler-product identity
  for middle extensions.

## Main statements

- `AlgebraicGeometry.WeilGroup.norm_le_of_hasEigenvalue_compactTopFrobenius`
- `AlgebraicGeometry.WeilGroup.le_radius_inv_tprod_eulerFactor`
- `AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_add_two`
- `AlgebraicGeometry.BoundaryDatum.sq_norm_le_rpow_of_hasEigenvalue_boundaryFrobenius`
- `AlgebraicGeometry.BoundaryDatum.frobeniusWeight_eq_of_isPunctuallyPure`
-/

@[expose] public section

universe u

open CategoryTheory

open scoped PowerSeries.WithPiTopology NNReal ENNReal

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K]

namespace WeilGroup

variable {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p) (l : ℕ)
  [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V)
  (ι : PadicAlgCl l →+* ℂ)

section TopCohomology

/-- The eigenvalues of the geometric Frobenius on `H_c² (U, ℱ) = V_{π₁(U)} (-1)` are bounded by
`q ^ (β / 2 + 1)` if `ℱ` has weights at most `β`.

Since `π₁(U)` acts trivially on the coinvariants, a local Frobenius `F_x` of degree `e` acts on
them as `γ ^ e`. If `μ` is an eigenvalue of `q γ`, then `(μ / q) ^ e` is an eigenvalue of `F_x` on
the quotient `V_{π₁(U)}` of `V`, hence of `F_x` on `V` (`lemma-filtrations-spectra--2`), so it has
weight at most `β`. -/
theorem norm_le_of_hasEigenvalue_compactTopFrobenius {β : ℝ} (hw : W.HasWeightsAtMost l ρ ι β)
    (x : C.finitePoints) {μ : PadicAlgCl l}
    (hμ : (W.compactTopFrobenius l ρ).HasEigenvalue μ) :
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
  have hwt := hw x _ hmem
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

end TopCohomology

section Radius

open PowerSeries

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
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f.coeff p.1 * g.coeff p.2‖ * r ^ n
      ≤ (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖f.coeff p.1‖ * ‖g.coeff p.2‖) * r ^ n := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_mul_le _ _)
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, pow_add]
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

variable {W l ρ ι}

/-- The local polynomial `ι P_x (ρ, T ^ e_x)` at a closed point `x`, the inverse of the Euler
factor at `x`. -/
private noncomputable abbrev localPoly (x : C.finitePoints) : Polynomial ℂ :=
  ((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ p.degreeOver x.1)

private theorem eulerFactor_eq (x : C.finitePoints) :
    W.eulerFactor l ρ ι x = ((localPoly (W := W) (l := l) (ρ := ρ) (ι := ι) x :
      Polynomial ℂ) : PowerSeries ℂ)⁻¹ := rfl

private theorem constantCoeff_localPoly (x : C.finitePoints) :
    constantCoeff ((localPoly (W := W) (l := l) (ρ := ρ) (ι := ι) x : Polynomial ℂ) :
      PowerSeries ℂ) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_pow,
    Polynomial.eval_X, zero_pow (p.degreeOver_ne_zero x.2), eval_zero_map_localPolynomial]

/-- The local factor at `x` is `1` modulo `T ^ e_x`. -/
private theorem X_pow_dvd_eulerFactor_sub_one (x : C.finitePoints) :
    X ^ p.degreeOver x.1 ∣ W.eulerFactor l ρ ι x - 1 := by
  have hP : (Polynomial.X : Polynomial ℂ) ∣ (W.localPolynomial l ρ x).map ι - 1 := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_zero_eq_eval_zero,
      eval_zero_map_localPolynomial, Polynomial.coeff_one_zero, sub_self]
  obtain ⟨R, hR⟩ := hP
  have hQ : (Polynomial.X : Polynomial ℂ) ^ p.degreeOver x.1 ∣
      localPoly (W := W) (l := l) (ρ := ρ) (ι := ι) x - 1 :=
    ⟨R.comp (Polynomial.X ^ p.degreeOver x.1), by
      rw [localPoly, ← Polynomial.one_comp (p := Polynomial.X ^ _), ← Polynomial.sub_comp, hR,
        Polynomial.mul_comp, Polynomial.X_comp]⟩
  have hQ' := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) hQ
  simp only [map_pow, map_sub, map_one, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X] at hQ'
  have h := X_pow_dvd_inv_sub_inv (n := p.degreeOver x.1)
    (by rw [constantCoeff_localPoly]; exact one_ne_zero) (by simp) hQ'
  rwa [inv_one, ← eulerFactor_eq] at h

/-- The closed points of `T` of degree at most `n`. -/
private noncomputable def lowDegree (T : Set C.finitePoints) (n : ℕ) : Finset T :=
  ((p.finite_setOf_degreeOver_le n).preimage Subtype.val_injective.injOn).toFinset

private theorem mem_lowDegree {T : Set C.finitePoints} {n : ℕ} {x : T} :
    x ∈ lowDegree (p := p) T n ↔ p.degreeOver x.1.1 ≤ n := by
  simp [lowDegree]

private theorem X_pow_dvd_eulerFactor_sub_one_of_notMem {T : Set C.finitePoints} {n : ℕ}
    {x : T} (hx : x ∉ lowDegree (p := p) T n) :
    X ^ (n + 1) ∣ W.eulerFactor l ρ ι x.1 - 1 := by
  rw [mem_lowDegree, not_le] at hx
  exact (pow_dvd_pow X hx).trans (X_pow_dvd_eulerFactor_sub_one x.1)

variable (W l ρ ι) in
/-- The Euler series over a set `T` of closed points has constant term `1`. -/
theorem constantCoeff_tprod_eulerFactor (T : Set C.finitePoints) :
    constantCoeff (∏' x : T, W.eulerFactor l ρ ι x.1) = 1 := by
  have hS (m : ℕ) : ∀ x ∉ lowDegree (p := p) T m, X ^ (m + 1) ∣ W.eulerFactor l ρ ι x.1 - 1 :=
    fun x hx ↦ X_pow_dvd_eulerFactor_sub_one_of_notMem hx
  rw [← coeff_zero_eq_constantCoeff_apply, WithPiTopology.coeff_tprod_of_X_pow_dvd_sub_one
    (lowDegree (p := p) T) hS _ (hS 0) le_rfl, coeff_zero_eq_constantCoeff_apply, map_prod]
  exact Finset.prod_eq_one fun x _ ↦ constantCoeff_eulerFactor ι x.1

/-- The coefficients of degree at most `n` of the inverse of the Euler series over `T` are those
of the finite product of the local polynomials at the points of degree at most `n`. -/
private theorem coeff_inv_tprod_eulerFactor (T : Set C.finitePoints) (n : ℕ) :
    coeff n (∏' x : T, W.eulerFactor l ρ ι x.1)⁻¹ =
      (∏ x ∈ lowDegree (p := p) T n,
        localPoly (W := W) (l := l) (ρ := ρ) (ι := ι) x.1).coeff n := by
  set S := lowDegree (p := p) T n
  set L := ∏' x : T, W.eulerFactor l ρ ι x.1
  set F : PowerSeries ℂ := ∏ x ∈ S, W.eulerFactor l ρ ι x.1
  have hS (m : ℕ) : ∀ x ∉ lowDegree (p := p) T m, X ^ (m + 1) ∣ W.eulerFactor l ρ ι x.1 - 1 :=
    fun x hx ↦ X_pow_dvd_eulerFactor_sub_one_of_notMem hx
  have hcoeff (k : ℕ) (hk : k ≤ n) : coeff k L = coeff k F :=
    WithPiTopology.coeff_tprod_of_X_pow_dvd_sub_one (lowDegree (p := p) T) hS S (hS n) hk
  have hF0 : constantCoeff F = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun x _ ↦ constantCoeff_eulerFactor ι x.1
  have hL0 : constantCoeff L = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hcoeff 0 (Nat.zero_le _),
      coeff_zero_eq_constantCoeff_apply, hF0]
  have hLF : X ^ (n + 1) ∣ L - F := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hcoeff m (Nat.lt_succ_iff.1 hm), sub_self]
  have hinv := X_pow_dvd_inv_sub_inv (by rw [hL0]; exact one_ne_zero)
    (by rw [hF0]; exact one_ne_zero) hLF
  have hFinv : F⁻¹ = ((∏ x ∈ S, localPoly (W := W) (l := l) (ρ := ρ) (ι := ι) x.1 :
      Polynomial ℂ) : PowerSeries ℂ) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by rw [hF0]; exact one_ne_zero),
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ ↦ by
      rw [eulerFactor_eq, Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.mul_inv_cancel _
        (by rw [constantCoeff_localPoly]; exact one_ne_zero)]
  rw [X_pow_dvd_iff] at hinv
  rw [← Polynomial.coeff_coe, ← hFinv, ← sub_eq_zero, ← map_sub]
  exact hinv n (Nat.lt_succ_self n)

/-- The complex local eigenvalues at a point of weight at most `β` are bounded by
`q ^ (e_x β / 2)`. -/
private theorem norm_le_of_frobeniusWeight_le {β : ℝ} {x : C.finitePoints}
    {α : PadicAlgCl l} (hα : α ∈ W.localEigenvalues l ρ x)
    (hw : frobeniusWeight ι (C.pointNorm x.1) α ≤ β) :
    ‖ι α‖ ≤ ((Nat.card K : ℝ) ^ (β / 2)) ^ p.degreeOver x.1 := by
  have hα0 : ι α ≠ 0 := (map_ne_zero ι).2 fun h ↦ zero_notMem_localEigenvalues x (h ▸ hα)
  rw [frobeniusWeight_le_iff ι (C.one_lt_pointNorm x.2) hα0,
    Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2] at hw
  have hq0 : (0 : ℝ) < Nat.card K := by exact_mod_cast Nat.card_pos (α := K)
  have heq : (((Nat.card K : ℝ) ^ (β / 2)) ^ p.degreeOver x.1) ^ 2 =
      ((Nat.card K ^ p.degreeOver x.1 : ℕ) : ℝ) ^ β := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (((Nat.card K : ℝ) ^ (β / 2)) ^ p.degreeOver x.1) 2,
      ← Real.rpow_natCast ((Nat.card K : ℝ) ^ (β / 2)) (p.degreeOver x.1),
      ← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le,
      ← Real.rpow_natCast (Nat.card K : ℝ) (p.degreeOver x.1), ← Real.rpow_mul hq0.le]
    congr 1
    push_cast
    ring
  have h2 : ‖ι α‖ ^ 2 ≤ ((((Nat.card K : ℝ) ^ (β / 2)) ^ p.degreeOver x.1)) ^ 2 :=
    heq ▸ hw
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- The weighted norm of the local polynomial at a point of weights at most `β`. -/
private theorem wnorm_localPoly_le {r : ℝ} (hr : 0 ≤ r) {β : ℝ} (x : C.finitePoints)
    (hw : ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β) :
    wnorm r (localPoly (W := W) (l := l) (ρ := ρ) (ι := ι) x) ≤
      Real.exp (Module.finrank (PadicAlgCl l) V *
        ((Nat.card K : ℝ) ^ (β / 2) * r) ^ p.degreeOver x.1) := by
  set e := p.degreeOver x.1
  set c : ℝ := ((Nat.card K : ℝ) ^ (β / 2) * r) ^ e
  have hc : 0 ≤ c := by positivity
  rw [localPoly, map_localPolynomial, Polynomial.multiset_prod_comp, Multiset.map_map]
  refine (wnorm_multiset_prod_le hr _).trans ?_
  rw [Multiset.map_map]
  have hle : ∀ a ∈ (W.localEigenvalues l ρ x).map ι,
      wnorm r ((1 - Polynomial.C a * Polynomial.X).comp (Polynomial.X ^ e)) ≤ 1 + c := by
    intro a ha
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 ha
    rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp]
    refine (wnorm_one_sub_C_mul_X_pow_le hr _ _).trans ?_
    gcongr
    calc ‖ι α‖ * r ^ e ≤ ((Nat.card K : ℝ) ^ (β / 2)) ^ e * r ^ e := by
          gcongr
          exact norm_le_of_frobeniusWeight_le hα (hw α hα)
      _ = c := by simp only [c, mul_pow]
  calc _ ≤ (((W.localEigenvalues l ρ x).map ι).map fun _ ↦ 1 + c).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun a _ ↦ wnorm_nonneg hr _) fun a ha ↦ hle a ha
    _ = (1 + c) ^ ((W.localEigenvalues l ρ x).card) := by simp
    _ ≤ (1 + c) ^ Module.finrank (PadicAlgCl l) V := by
        refine pow_le_pow_right₀ (by linarith) ?_
        rw [localEigenvalues, ← LinearMap.charpoly_natDegree (ρ (W.frobenius x))]
        exact Polynomial.card_roots' _
    _ ≤ Real.exp c ^ Module.finrank (PadicAlgCl l) V := by
        gcongr
        linarith [Real.add_one_le_exp c]
    _ = Real.exp (Module.finrank (PadicAlgCl l) V * c) := by
        rw [← Real.exp_nat_mul]

variable (W l ρ ι)

/-- Step 1 of `proposition-weights-j-boundary-points--1`: the pole-free region of the open part.

Let `T` be a set of closed points of `C₀` with at most `A q ^ e` points of degree `e`, and let
`ℱ` have weights at most `β` at the points of `T`. Then the inverse of the partial Euler series
`∏_{x ∈ T} ι P_x (ℱ, T ^ e_x)⁻¹` converges on the disc of radius `r` whenever
`q ^ (β / 2 + 1) r < 1`.

The coefficient of degree `n` of the inverse is that of the finite product of the local
polynomials at the points of degree at most `n`, whose weighted norm `∑ₙ |aₙ| rⁿ` is at most
`∏_x (1 + (q ^ (β / 2) r) ^ e_x) ^ rank ≤ exp (rank ∑_x (q ^ (β / 2) r) ^ e_x)`; grouping the
points by degree, the exponent is at most `rank A ∑_e (q ^ (β / 2 + 1) r) ^ e < ∞`. -/
theorem le_radius_inv_tprod_eulerFactor (T : Set C.finitePoints) {β : ℝ}
    (hw : ∀ x ∈ T, ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β)
    {A : ℝ} (hA : ∀ (s : Finset T) (e : ℕ),
      ((s.filter fun x ↦ p.degreeOver x.1.1 = e).card : ℝ) ≤ A * (Nat.card K : ℝ) ^ e)
    {r : ℝ≥0} (hr : (Nat.card K : ℝ) ^ (β / 2 + 1) * r < 1) :
    (r : ℝ≥0∞) ≤ (∏' x : T, W.eulerFactor l ρ ι x.1)⁻¹.radius := by
  classical
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; exact_mod_cast Nat.card_pos (α := K)
  set c : ℝ := q ^ (β / 2) * r
  have hc : 0 ≤ c := by positivity
  have hqc : q * c < 1 := by
    rw [show q * c = q ^ (β / 2 + 1) * r by
      rw [Real.rpow_add hq0, Real.rpow_one]; ring]
    exact hr
  have hA0 : 0 ≤ A := by
    have h := hA ∅ 0
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, pow_zero, mul_one] at h
    exact h
  set d : ℝ := (Module.finrank (PadicAlgCl l) V : ℝ)
  set B : ℝ := A * ∑' e : ℕ, (q * c) ^ e
  have hgeom : Summable fun e : ℕ ↦ (q * c) ^ e :=
    summable_geometric_of_lt_one (by positivity) hqc
  -- the sum of `c ^ e_x` over a finite set of points of `T` is at most `B`
  have hsum (s : Finset T) : ∑ x ∈ s, c ^ p.degreeOver x.1.1 ≤ B := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : T ↦ p.degreeOver x.1.1)
      (t := s.image fun x : T ↦ p.degreeOver x.1.1) fun x hx ↦ Finset.mem_image_of_mem _ hx]
    calc ∑ e ∈ s.image fun x : T ↦ p.degreeOver x.1.1,
          ∑ x ∈ s with p.degreeOver x.1.1 = e, c ^ p.degreeOver x.1.1
        = ∑ e ∈ s.image fun x : T ↦ p.degreeOver x.1.1,
            ((s.filter fun x ↦ p.degreeOver x.1.1 = e).card : ℝ) * c ^ e := by
          refine Finset.sum_congr rfl fun e _ ↦ ?_
          rw [Finset.sum_congr rfl fun x hx ↦ by rw [(Finset.mem_filter.1 hx).2],
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ e ∈ s.image fun x : T ↦ p.degreeOver x.1.1, A * (q * c) ^ e := by
          refine Finset.sum_le_sum fun e _ ↦ ?_
          have h := mul_le_mul_of_nonneg_right (hA s e) (pow_nonneg hc e)
          rwa [mul_assoc, ← mul_pow] at h
      _ = A * ∑ e ∈ s.image fun x : T ↦ p.degreeOver x.1.1, (q * c) ^ e := by
          rw [Finset.mul_sum]
      _ ≤ B := mul_le_mul_of_nonneg_left
          (hgeom.sum_le_tsum _ fun e _ ↦ by positivity) hA0
  refine PowerSeries.le_radius_of_bound (Real.exp (d * B)) fun n ↦ ?_
  rw [coeff_inv_tprod_eulerFactor]
  refine (norm_coeff_mul_pow_le_wnorm (by positivity) _ n).trans ?_
  refine (wnorm_prod_le (by positivity) _ _).trans ?_
  calc ∏ x ∈ lowDegree (p := p) T n, wnorm r (localPoly (W := W) (l := l) (ρ := ρ) (ι := ι) x.1)
      ≤ ∏ x ∈ lowDegree (p := p) T n, Real.exp (d * c ^ p.degreeOver x.1.1) :=
        Finset.prod_le_prod₀ (fun x _ ↦ wnorm_nonneg (by positivity) _)
          fun x _ ↦ wnorm_localPoly_le (by positivity) x.1 (hw x.1 x.2)
    _ = Real.exp (d * ∑ x ∈ lowDegree (p := p) T n, c ^ p.degreeOver x.1.1) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (d * B) := by
        gcongr
        exact hsum _

end Radius

end WeilGroup

namespace BoundaryDatum

variable {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p] {pU : U ⟶ Spec (.of K)}
  [IsCurve pU] {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU}
  {WC : WeilGroup p} (D : BoundaryDatum j WU WC) (l : ℕ) [Fact l.Prime] {V : Type u}
  [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ι : PadicAlgCl l →+* ℂ)

/-- The polynomial `ι det (1 - F_s T ^ e_s ∣ V ^ (I_s))` at a boundary point `s`, the inverse of
the local factor at `s` of the `L`-series of the middle extension `j_* ℱ`. -/
noncomputable def boundaryPolynomial (ρ : Representation (PadicAlgCl l) WU.carrier V)
    (s : ↥((Set.range j.base)ᶜ)) : Polynomial ℂ :=
  ((D.boundaryFrobenius l ρ s).charpolyRev.map ι).comp (Polynomial.X ^ p.degreeOver s.1)

/-- The Euler-product identity of `proposition-weights-j-boundary-points`, transported to the
representation side, as a hypothesis on a boundary datum. (The blueprint node itself is the
sheaf-level identity
`AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk_directImage`.)

Let `X'₀ ⊆ C₀` be an affine open, a smooth geometrically connected affine curve, and let
`j' : U'₀ = U₀ ∩ X'₀ ↪ X'₀`. For the middle extension `j'_* ℱ` of a lisse Weil sheaf `ℱ` the
Euler-product form of the Grothendieck–Lefschetz trace formula reads
`L (X'₀, j'_* ℱ, T) = det (1 - F T ∣ H_c¹) / det (1 - F T ∣ H_c²)`, as `H_c⁰ (X', j'_* ℱ) = 0`.
Its left-hand side is the Euler series of `ℱ` over the closed points of `U'₀` times the
boundary factors `ι det (1 - F_s T ^ e_s ∣ V ^ (I_s))⁻¹` at the points `s ∈ X'₀ \ U₀`, and
`H_c² (X', j'_* ℱ) = H_c² (U', ℱ) = V_{π₁(U)} (-1)` (`lemma-degree-zero-top-cohomology--2`, using
that `π₁(U') → π₁(U)` is onto). Clearing denominators: for some polynomial `P` (the numerator
`ι det (1 - F T ∣ H_c¹)`),
`L (U'₀, ℱ, T) · ι det (1 - F T ∣ H_c²) = P · ∏_{s ∈ X'₀ \ U₀} ι det (1 - F_s T ^ e_s ∣ V ^ (I_s))`.

For the boundary datum of the actual inertia groups and residue Frobenius lifts of an open
immersion this is the Grothendieck–Lefschetz trace formula, which is not available. It is not a
consequence of the fields of a `BoundaryDatum`: they tie the Weil groups and the restriction
map to the curve, but pin the inertia groups down only through the closed normal subgroup they
generate (`AlgebraicGeometry.BoundaryDatum.ker_restrict_eq`), and the boundary polynomials
depend on the individual inertia groups. It is therefore recorded as a hypothesis on `D`, for
every lisse Weil sheaf on `U₀` (the tensor-power argument applies it to `ℱ ^ ⊗ 2 ^ k` and to
`ℱ ^ ∨`). -/
def HasMiddleExtensionEulerProduct [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [Fact (ringChar K ≠ l)] : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    {X' : C.Opens}, IsAffineOpen X' → ∀ ρ : Representation (PadicAlgCl l) WU.carrier V,
    WU.IsLisse l ρ → ∃ P : Polynomial ℂ,
      (∏' x : {x : U.finitePoints | j.base x.1 ∈ X'}, WU.eulerFactor l ρ ι x.1) *
        (((WU.compactTopFrobenius l ρ).charpolyRev.map ι : Polynomial ℂ) : PowerSeries ℂ) =
      P * ((∏ᶠ s : {s : ↥((Set.range j.base)ᶜ) // s.1 ∈ X'},
        D.boundaryPolynomial l ι ρ s.1 : Polynomial ℂ) : PowerSeries ℂ)

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- The eigenvalues of the boundary Frobenius are nonzero, since `F_s` acts invertibly. -/
theorem ne_zero_of_hasEigenvalue_boundaryFrobenius
    (ρ : Representation (PadicAlgCl l) WU.carrier V) (s : ↥((Set.range j.base)ᶜ))
    {α : PadicAlgCl l} (hα : (D.boundaryFrobenius l ρ s).HasEigenvalue α) : α ≠ 0 := by
  rintro rfl
  obtain ⟨⟨v, hv⟩, hvec⟩ := hα.exists_hasEigenvector
  have h0 : ρ (D.residueFrobenius s) v = 0 := by
    simpa [boundaryFrobenius] using congrArg Subtype.val hvec.apply_eq_smul
  have : v = 0 := by
    have hv' : v = ρ (D.residueFrobenius s)⁻¹ (ρ (D.residueFrobenius s) v) := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hv', h0, map_zero]
  exact hvec.2 (Subtype.ext this)

/-- The boundary polynomial at `s` takes the value `1` at `0`. -/
theorem eval_zero_boundaryPolynomial (ρ : Representation (PadicAlgCl l) WU.carrier V)
    (s : ↥((Set.range j.base)ᶜ)) : (D.boundaryPolynomial l ι ρ s).eval 0 = 1 := by
  rw [boundaryPolynomial, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
    zero_pow (p.degreeOver_ne_zero (D.boundary_subset_finitePoints s.2)),
    LinearMap.charpolyRev_eq_prod_roots, Polynomial.map_multiset_prod_one_sub_C_mul_X,
    Polynomial.eval_multiset_prod, Multiset.map_map]
  exact Multiset.prod_eq_one fun a ha ↦ by
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
    simp

/-- An eigenvalue `α` of the boundary Frobenius at `s` gives a zero `z` of the boundary
polynomial at `s`, with `z ^ e_s = (ι α)⁻¹`. -/
theorem eval_boundaryPolynomial_eq_zero (ρ : Representation (PadicAlgCl l) WU.carrier V)
    (s : ↥((Set.range j.base)ᶜ)) {α : PadicAlgCl l}
    (hα : (D.boundaryFrobenius l ρ s).HasEigenvalue α) {z : ℂ}
    (hz : z ^ p.degreeOver s.1 = (ι α)⁻¹) : (D.boundaryPolynomial l ι ρ s).eval z = 0 := by
  have hα0 : ι α ≠ 0 := (map_ne_zero ι).2 (D.ne_zero_of_hasEigenvalue_boundaryFrobenius l ρ s hα)
  have hroot : α ∈ (D.boundaryFrobenius l ρ s).charpoly.roots := by
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hα
  rw [boundaryPolynomial, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, hz,
    LinearMap.charpolyRev_eq_prod_roots, Polynomial.map_multiset_prod_one_sub_C_mul_X,
    Polynomial.eval_multiset_prod]
  refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨1 - Polynomial.C (ι α) * Polynomial.X,
    Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem ι hroot), ?_⟩)
  simp [hα0]

include D in
/-- The closed points of `U₀` lying in an affine open `X'₀` of `C₀` satisfy the point count bound
of `lemma-point-count-bound--1`: there is `A` with at most `A q ^ e` points of degree `e`
among them. -/
theorem exists_card_filter_degreeOver_le {X' : C.Opens} (hX' : IsAffineOpen X') :
    ∃ A : ℝ, ∀ (t : Finset {x : U.finitePoints | j.base x.1 ∈ X'}) (e : ℕ),
      ((t.filter fun x ↦ pU.degreeOver x.1.1 = e).card : ℝ) ≤ A * (Nat.card K : ℝ) ^ e := by
  classical
  have : IsAffine X'.toScheme := hX'
  have hdim : topologicalKrullDim X'.toScheme ≤ 1 :=
    (topologicalKrullDim_subspace_le C X').trans (IsCurve.krullDim_le_one p)
  obtain ⟨d, hd⟩ := (X'.ι ≫ p).exists_pointCount_le_mul_pow hdim
  have hdeg (x : U) : pU.degreeOver x = p.degreeOver (j.base x) := by
    rw [← Scheme.Hom.degreeOver_comp_of_isIso, D.comp_eq]
  refine ⟨d, fun t e ↦ ?_⟩
  rcases eq_or_ne e 0 with rfl | he
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ ↦
      pU.degreeOver_ne_zero x.1.2)]
    simp
  -- the points of `t` of degree `e`, as points of `X'₀`
  let φ : {x : U.finitePoints | j.base x.1 ∈ X'} → X'.toScheme.finitePoints := fun x ↦
    ⟨⟨j.base x.1.1, x.2⟩, (Scheme.Hom.mem_finitePoints_iff_of_isIso X'.ι _).1
      ((Scheme.Hom.mem_finitePoints_iff_of_isIso j x.1.1).2 x.1.2)⟩
  have hφ : Function.Injective φ := fun x y h ↦ by
    have h' : j.base x.1.1 = j.base y.1.1 := congrArg (fun z ↦ z.1.1) h
    exact Subtype.ext (Subtype.ext (j.isOpenEmbedding.injective h'))
  have hφdeg (x : {x : U.finitePoints | j.base x.1 ∈ X'}) :
      (X'.ι ≫ p).degreeOver (φ x).1 = pU.degreeOver x.1.1 := by
    rw [Scheme.Hom.degreeOver_comp_of_isIso, hdeg]
    rfl
  set S := (t.filter fun x ↦ pU.degreeOver x.1.1 = e).image φ
  have hS : S.card = (t.filter fun x ↦ pU.degreeOver x.1.1 = e).card :=
    Finset.card_image_of_injective _ hφ
  set T' := ((X'.ι ≫ p).finite_setOf_degreeOver_le e).toFinset
  have hcount := (X'.ι ≫ p).pointCount_eq_sum he (T := T') fun y hy ↦ by
    simpa [T'] using Nat.le_of_dvd (Nat.pos_of_ne_zero he) hy
  have hST : S ⊆ T'.filter fun y ↦ (X'.ι ≫ p).degreeOver y.1 ∣ e := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hxe := (Finset.mem_filter.1 hx).2
    simp [T', hφdeg, hxe]
  have hle : S.card ≤ (X'.ι ≫ p).pointCount e := by
    rw [hcount]
    calc S.card = ∑ y ∈ S, 1 := by simp
      _ ≤ ∑ y ∈ S, (X'.ι ≫ p).degreeOver y.1 := Finset.sum_le_sum fun y _ ↦
          Nat.one_le_iff_ne_zero.2 ((X'.ι ≫ p).degreeOver_ne_zero y.2)
      _ ≤ _ := Finset.sum_le_sum_of_subset hST
  rw [← hS]
  exact_mod_cast hle.trans (hd e he)

/-- Steps 0–3 of `proposition-weights-j-boundary-points--1`: the preliminary bound.

If `ℱ` is lisse with weights at most `β` on `U₀`, every eigenvalue `α` of the residue Frobenius
on the boundary stalk at `s` has weight at most `β + 2`.

On an affine neighbourhood `X'₀` of `s`, the inverse of the Euler series of `ℱ` over
`U'₀ = U₀ ∩ X'₀` and `P / ι det (1 - F T ∣ H_c²)` converge on the disc of radius
`R = q ^ (-(β / 2 + 1))` (`AlgebraicGeometry.WeilGroup.le_radius_inv_tprod_eulerFactor`,
`AlgebraicGeometry.WeilGroup.norm_le_of_hasEigenvalue_compactTopFrobenius`); by the Euler product
identity (`proposition-weights-j-boundary-points`) so does the inverse of the product of the
boundary polynomials, which therefore has no zero in that disc. The zero `z` with
`z ^ e_s = (ι α)⁻¹` gives `|ι α| ^ (-1 / e_s) ≥ R`. -/
theorem frobeniusWeight_le_add_two [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [Fact (ringChar K ≠ l)]
    (hD : D.HasMiddleExtensionEulerProduct l ι)
    (ρ : Representation (PadicAlgCl l) WU.carrier V)
    (hρ : WU.IsLisse l ρ) {β : ℝ} (hw : WU.HasWeightsAtMost l ρ ι β)
    (s : ↥((Set.range j.base)ᶜ)) {α : PadicAlgCl l}
    (hα : (D.boundaryFrobenius l ρ s).HasEigenvalue α) :
    WeilGroup.frobeniusWeight ι (C.pointNorm s.1) α ≤ β + 2 := by
  classical
  open PowerSeries in
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq : 1 < q := by
    have := (Finite.one_lt_card_iff_nontrivial (α := K)).2 inferInstance
    rw [hqdef]
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hsfin : s.1 ∈ C.finitePoints := D.boundary_subset_finitePoints s.2
  set e := p.degreeOver s.1
  have he : e ≠ 0 := p.degreeOver_ne_zero hsfin
  -- an affine neighbourhood `X'₀` of `s` and the closed points of `U'₀ = U₀ ∩ X'₀`
  obtain ⟨X', hX', hsX', -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s.1) trivial
  set T : Set U.finitePoints := {x | j.base x.1 ∈ X'}
  obtain ⟨A, hA⟩ := D.exists_card_filter_degreeOver_le hX'
  -- the eigenvalues of the geometric Frobenius on `H_c²`
  obtain ⟨x₀, hx₀⟩ := pU.exists_mem_finitePoints
  set S := (WU.compactTopFrobenius l ρ).charpoly.roots.map ι
  have hS : ∀ c ∈ S, ‖c‖ ≤ q ^ (β / 2 + 1) := by
    intro c hc
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hc
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hμ
    exact WU.norm_le_of_hasEigenvalue_compactTopFrobenius l ρ ι hw ⟨x₀, hx₀⟩ hμ
  set R : ℝ := q ^ (-(β / 2 + 1))
  have hR : 0 < R := Real.rpow_pos_of_pos hq0 _
  have hRq : q ^ (β / 2 + 1) * R = 1 := by
    rw [← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  -- the Euler product identity
  obtain ⟨P, hP⟩ := hD hX' ρ hρ
  set L := ∏' x : T, WU.eulerFactor l ρ ι x.1
  set Dser : PowerSeries ℂ :=
    (((WU.compactTopFrobenius l ρ).charpolyRev.map ι : Polynomial ℂ) : PowerSeries ℂ)
    with hDdef
  have hDser : Dser = (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod := by
    rw [hDdef, LinearMap.charpolyRev_eq_prod_roots, Polynomial.map_multiset_prod_one_sub_C_mul_X,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun c _ ↦ by simp)
  have hDser0 : PowerSeries.constantCoeff Dser = 1 := by
    rw [hDser, map_multiset_prod, Multiset.map_map, Multiset.prod_eq_one fun a ha ↦ by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
      simp]
  have hL0 : PowerSeries.constantCoeff L = 1 := WU.constantCoeff_tprod_eulerFactor l ρ ι T
  have : Finite {s : ↥((Set.range j.base)ᶜ) // s.1 ∈ X'} :=
    have := D.finite_boundary.to_subtype
    Subtype.finite
  set B : Polynomial ℂ := ∏ᶠ s : {s : ↥((Set.range j.base)ᶜ) // s.1 ∈ X'},
    D.boundaryPolynomial l ι ρ s.1 with hBdef
  have hev (z : ℂ) : B.eval z =
      ∏ᶠ s : {s : ↥((Set.range j.base)ᶜ) // s.1 ∈ X'}, (D.boundaryPolynomial l ι ρ s.1).eval z := by
    have := MonoidHom.map_finprod (Polynomial.evalRingHom z : Polynomial ℂ →* ℂ)
      (f := fun s : {s : ↥((Set.range j.base)ᶜ) // s.1 ∈ X'} ↦ D.boundaryPolynomial l ι ρ s.1)
      (Set.toFinite _)
    simpa [hBdef] using this
  have hB0 : B.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev]
    simp only [eval_zero_boundaryPolynomial, finprod_one]
    exact one_ne_zero
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
  -- the zero `z` of the boundary polynomial at `s`
  have hα0 : ι α ≠ 0 :=
    (map_ne_zero ι).2 (D.ne_zero_of_hasEigenvalue_boundaryFrobenius l ρ s hα)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι α)⁻¹ (Nat.pos_of_ne_zero he)
  have hBz : B.eval z = 0 := by
    rw [hev]
    exact finprod_eq_zero _ ⟨s, hsX'⟩ (D.eval_boundaryPolynomial_eq_zero l ι ρ s hα hz)
      (Set.toFinite _)
  -- the zero lies outside the disc of radius `R`
  have hzR : R ≤ ‖z‖ := by
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
    have h1 : (r : ENNReal) ≤ ((P : PowerSeries ℂ) * Dser⁻¹).radius := by
      rw [hDser]
      exact PowerSeries.le_radius_coe_mul_inv_prod P S hr
    have h2 : (r : ENNReal) ≤ L⁻¹.radius :=
      WU.le_radius_inv_tprod_eulerFactor l ρ ι T (fun x _ ↦ hw x) hA (by
        calc q ^ (β / 2 + 1) * r < q ^ (β / 2 + 1) * R :=
              mul_lt_mul_of_pos_left hrR (by positivity)
          _ = 1 := hRq)
    have h3 : (‖z‖₊ : ENNReal) < ((B : PowerSeries ℂ)⁻¹).radius := by
      rw [hBinv]
      exact lt_of_lt_of_le (by exact_mod_cast hzr)
        ((le_min h1 h2).trans (PowerSeries.min_radius_le_radius_mul _ _))
    exact PowerSeries.eval_ne_zero_of_lt_radius_inv hB0 h3 hBz
  -- hence `|ι α| ≤ q ^ (e (β / 2 + 1))`
  have hnorm : ‖ι α‖ ≤ q ^ ((e : ℝ) * (β / 2 + 1)) := by
    have hze : ‖z‖ ^ e = ‖ι α‖⁻¹ := by rw [← norm_pow, hz, norm_inv]
    have hRe : R ^ e ≤ ‖ι α‖⁻¹ := hze ▸ pow_le_pow_left₀ hR.le hzR e
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le] at hRe
    have := (le_inv_comm₀ (by positivity) (norm_pos_iff.2 hα0)).1 hRe
    rwa [← Real.rpow_neg hq0.le, neg_mul, neg_neg, mul_comm] at this
  rw [WeilGroup.frobeniusWeight, Scheme.Hom.pointNorm_eq_pow_degreeOver p hsfin, Nat.cast_pow,
    Real.log_pow, div_le_iff₀ (mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)) (Real.log_pos hq))]
  have := Real.log_le_log (norm_pos_iff.2 hα0) hnorm
  rw [Real.log_rpow hq0] at this
  change 2 * Real.log ‖ι α‖ ≤ (β + 2) * (e * Real.log q)
  nlinarith

/-- If `α` is an eigenvalue of the boundary Frobenius of `ℱ` at `s`, then `α ^ 2` is one of
`ℱ ⊗ ℱ`: for an invariant eigenvector `v`, the vector `v ⊗ v` is an invariant eigenvector
(`lemma-filtrations-spectra`). -/
theorem hasEigenvalue_boundaryFrobenius_tprod_self
    {ρ : Representation (PadicAlgCl l) WU.carrier V} {s : ↥((Set.range j.base)ᶜ)}
    {α : PadicAlgCl l} (hα : (D.boundaryFrobenius l ρ s).HasEigenvalue α) :
    (D.boundaryFrobenius l (ρ.tprod ρ) s).HasEigenvalue (α ^ 2) := by
  obtain ⟨⟨v, hv⟩, hvec⟩ := hα.exists_hasEigenvector
  have hFv : ρ (D.residueFrobenius s) v = α • v := by
    simpa [boundaryFrobenius] using congrArg Subtype.val hvec.apply_eq_smul
  have hv0 : v ≠ 0 := fun h ↦ hvec.2 (Subtype.ext h)
  have hvv : v ⊗ₜ[PadicAlgCl l] v ∈ D.boundaryStalk l (ρ.tprod ρ) s := by
    rw [boundaryStalk, Representation.mem_invariants] at hv ⊢
    intro g
    have hg := hv g
    simp only [MonoidHom.coe_comp, Function.comp_apply] at hg
    simp only [MonoidHom.coe_comp, Function.comp_apply, Representation.tprod_apply,
      TensorProduct.map_tmul]
    rw [hg]
  have hvv0 : v ⊗ₜ[PadicAlgCl l] v ≠ 0 := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (PadicAlgCl l) hv0
    intro h
    have := congrArg (TensorProduct.lift ((LinearMap.mul (PadicAlgCl l) (PadicAlgCl l)).compl₁₂
      φ φ)) h
    simp only [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      map_zero, mul_self_eq_zero] at this
    exact hφ this
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨_, hvv⟩) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    ext
    simp only [boundaryFrobenius, LinearMap.restrict_apply, Representation.tprod_apply,
      TensorProduct.map_tmul, hFv, SetLike.val_smul]
    rw [TensorProduct.smul_tmul_smul, sq]
  · exact fun h ↦ hvv0 (congrArg Subtype.val h)

/-- Step 4 of `proposition-weights-j-boundary-points--1`: sharpening by tensor powers.

Applying the preliminary bound to the iterated tensor squares `ℱ ^ ⊗ 2 ^ k`, whose weights are
at most `2 ^ k β` and whose boundary Frobenius has the eigenvalue `α ^ (2 ^ k)`, gives
`wt (α) ≤ β + 2 / 2 ^ k`. -/
theorem frobeniusWeight_le_add_div_two_pow [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
    (hD : D.HasMiddleExtensionEulerProduct l ι) (k : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
      [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) WU.carrier V),
      WU.IsLisse l ρ → ∀ {β : ℝ}, WU.HasWeightsAtMost l ρ ι β →
      ∀ (s : ↥((Set.range j.base)ᶜ)) {α : PadicAlgCl l},
        (D.boundaryFrobenius l ρ s).HasEigenvalue α →
        WeilGroup.frobeniusWeight ι (C.pointNorm s.1) α ≤ β + 2 / 2 ^ k := by
  induction k with
  | zero =>
    intro V _ _ _ ρ hρ β hw s α hα
    simpa using D.frobeniusWeight_le_add_two l ι hD ρ hρ hw s hα
  | succ k ih =>
    intro V _ _ _ ρ hρ β hw s α hα
    have h := ih (ρ.tprod ρ) (hρ.tprod hρ) (hw.tprod_self ι) s
      (D.hasEigenvalue_boundaryFrobenius_tprod_self l hα)
    rw [WeilGroup.frobeniusWeight_pow] at h
    have h2 : (2 : ℝ) / 2 ^ (k + 1) = 2 / 2 ^ k / 2 := by rw [pow_succ]; ring
    rw [h2]
    push_cast at h
    linarith

/-- `proposition-weights-j-boundary-points--1` in terms of weights: if `ℱ` is lisse with weights at
most `β` on `U₀`, every eigenvalue of the residue Frobenius on the boundary stalk at `s` has weight
at most `β`. -/
theorem frobeniusWeight_le_of_hasEigenvalue_boundaryFrobenius [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
    (hD : D.HasMiddleExtensionEulerProduct l ι)
    (ρ : Representation (PadicAlgCl l) WU.carrier V) (hρ : WU.IsLisse l ρ) {β : ℝ}
    (hw : WU.HasWeightsAtMost l ρ ι β) (s : ↥((Set.range j.base)ᶜ)) {α : PadicAlgCl l}
    (hα : (D.boundaryFrobenius l ρ s).HasEigenvalue α) :
    WeilGroup.frobeniusWeight ι (C.pointNorm s.1) α ≤ β := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε) one_half_lt_one
  have h := D.frobeniusWeight_le_add_div_two_pow l ι hD k ρ hρ hw s hα
  have hk' : (2 : ℝ) / 2 ^ k < ε := by
    rw [one_div_pow] at hk
    have : (2 : ℝ) / 2 ^ k = 2 * (1 / 2 ^ k) := by ring
    rw [this]
    linarith
  linarith

/-- Boundary semicontinuity of weights on a curve (`proposition-weights-j-boundary-points--1`), on
the representation side and conditional on the Euler-product hypothesis `hD`.

Let `j : U₀ ↪ C₀` be a dense open of a smooth geometrically connected curve over `𝔽_q` with
finite complement, and let `ℱ` be a lisse Weil sheaf on `U₀` such that every local Frobenius
eigenvalue `α` at a closed point `x` of `U₀` satisfies `|ι α| ^ 2 ≤ q_x ^ β`. Then every
eigenvalue `α` of the residue Frobenius `F_s` on the boundary stalk `(j_* ℱ)_s̄ = V ^ (I_s)` at a
boundary point `s` satisfies `|ι α| ^ 2 ≤ q_s ^ β`.

Steps 0–3 (`AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_add_two`) give the bound
`q_s ^ (β + 2)` on an affine neighbourhood of `s`; Step 4 applies it to the tensor powers
(`AlgebraicGeometry.BoundaryDatum.frobeniusWeight_le_add_div_two_pow`). -/
theorem sq_norm_le_rpow_of_hasEigenvalue_boundaryFrobenius [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
    (hD : D.HasMiddleExtensionEulerProduct l ι)
    (ρ : Representation (PadicAlgCl l) WU.carrier V) (hρ : WU.IsLisse l ρ) {β : ℝ}
    (hβ : ∀ (x : U.finitePoints), ∀ α ∈ WU.localEigenvalues l ρ x,
      ‖ι α‖ ^ 2 ≤ (U.pointNorm x.1 : ℝ) ^ β)
    (s : ↥((Set.range j.base)ᶜ)) {α : PadicAlgCl l}
    (hα : (D.boundaryFrobenius l ρ s).HasEigenvalue α) :
    ‖ι α‖ ^ 2 ≤ (C.pointNorm s.1 : ℝ) ^ β := by
  have hw : WU.HasWeightsAtMost l ρ ι β := fun x a ha ↦
    (WeilGroup.frobeniusWeight_le_iff ι (U.one_lt_pointNorm x.2)
      ((map_ne_zero ι).2 fun h ↦ WeilGroup.zero_notMem_localEigenvalues x (h ▸ ha))).2
      (hβ x a ha)
  exact (WeilGroup.frobeniusWeight_le_iff ι
    (C.one_lt_pointNorm (D.boundary_subset_finitePoints s.2))
    ((map_ne_zero ι).2 (D.ne_zero_of_hasEigenvalue_boundaryFrobenius l ρ s hα))).1
    (D.frobeniusWeight_le_of_hasEigenvalue_boundaryFrobenius l ι hD ρ hρ hw s hα)

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- If inertia at `s` acts trivially, every eigenvalue of the residue Frobenius on `V` is an
eigenvalue of the boundary Frobenius at `s`, since the boundary stalk is all of `V`. -/
theorem hasEigenvalue_boundaryFrobenius_of_forall_inertia
    {ρ : Representation (PadicAlgCl l) WU.carrier V} {s : ↥((Set.range j.base)ᶜ)}
    (htriv : ∀ g ∈ D.inertia s, ρ g = 1) {α : PadicAlgCl l}
    (hα : Module.End.HasEigenvalue (ρ (D.residueFrobenius s)) α) :
    (D.boundaryFrobenius l ρ s).HasEigenvalue α := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hvs : v ∈ D.boundaryStalk l ρ s := by
    rw [boundaryStalk, Representation.mem_invariants]
    intro g
    simp [htriv g.1 g.2]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvs⟩) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    ext
    simp [boundaryFrobenius, hv.apply_eq_smul]
  · exact fun h ↦ hv.2 (congrArg Subtype.val h)

/-- Purity at an unramified boundary point (first part of `corollary-unramified-boundary-point--2`),
conditional on the Euler-product hypothesis `hD`.

Let `ℱ` be lisse and punctually `ι`-pure of weight `w` on `U₀`, and let `s` be a boundary point
at which the inertia `I_s` acts trivially. Then the extended stalk `(j_* ℱ)_s̄ = V` is pure of
weight `w`: every eigenvalue `α` of the residue Frobenius `F_s` on `V` has weight `w`.

By `proposition-weights-j-boundary-points--1` applied to `ℱ`, of weights at most `w`, the weight of
`α` is at most `w`; applied to the dual `ℱ ^ ∨`, punctually pure of weight `-w` and again unramified
at `s`, whose residue Frobenius has the eigenvalue `α⁻¹`, it is at least `w`. -/
theorem frobeniusWeight_eq_of_isPunctuallyPure [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)]
    (hD : D.HasMiddleExtensionEulerProduct l ι)
    (ρ : Representation (PadicAlgCl l) WU.carrier V) (hρ : WU.IsLisse l ρ) {w : ℝ}
    (hpure : WU.IsPunctuallyPure l ρ ι w) (s : ↥((Set.range j.base)ᶜ))
    (htriv : ∀ g ∈ D.inertia s, ρ g = 1) {α : PadicAlgCl l}
    (hα : Module.End.HasEigenvalue (ρ (D.residueFrobenius s)) α) :
    WeilGroup.frobeniusWeight ι (C.pointNorm s.1) α = w := by
  have hle := D.frobeniusWeight_le_of_hasEigenvalue_boundaryFrobenius l ι hD ρ hρ
    (fun x a ha ↦ (hpure x a ha).le) s (D.hasEigenvalue_boundaryFrobenius_of_forall_inertia l
      htriv hα)
  have htriv' : ∀ g ∈ D.inertia s, ρ.dual g = 1 := fun g hg ↦ by
    ext f v
    simp [Representation.dual_apply, Module.Dual.transpose_apply,
      htriv g⁻¹ ((D.inertia s).inv_mem hg)]
  have hα' : Module.End.HasEigenvalue (ρ.dual (D.residueFrobenius s)) α⁻¹ := by
    rw [Representation.hasEigenvalue_dual_iff]
    exact ρ.hasEigenvalue_inv hα
  have hge := D.frobeniusWeight_le_of_hasEigenvalue_boundaryFrobenius l ι hD ρ.dual hρ.dual
    (fun x a ha ↦ (hpure.dual ι x a ha).le) s
    (D.hasEigenvalue_boundaryFrobenius_of_forall_inertia l htriv' hα')
  rw [WeilGroup.frobeniusWeight_inv] at hge
  linarith

end BoundaryDatum

end AlgebraicGeometry
