/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# The radius of convergence of a formal power series

A formal power series `f = ∑ aₙ Tⁿ ∈ 𝕜⟦X⟧` over a nontrivially normed field has a radius of
convergence `R(f) ∈ ℝ≥0∞`, the supremum of all `r ≥ 0` such that `∑ₙ ‖aₙ‖ tⁿ` converges for
every `0 ≤ t < r`.

Rather than redoing the classical theory we reduce to Mathlib's radius of convergence of a
formal multilinear series: the scalar series `∑ aₙ Tⁿ` is `FormalMultilinearSeries.ofScalars`
applied to the coefficients of `f`, and `FormalMultilinearSeries.radius` of that series is the
usual radius of convergence.

This file also introduces nonnegative series, those all of whose complex coefficients lie in
`ℝ≥0`, and proves the comparison results of the real-sheaves chapter: a factor of a convergent
product of nonnegative series with constant term `1` has at least the radius of the product
(`lemma-positivity-convergence--1`), and a polynomial whose inverse has radius `R` has no zero in
the open disc of radius `R`.

## Main definitions

- `PowerSeries.radius` : the radius of convergence `R(f) ∈ ℝ≥0∞` of `f : 𝕜⟦X⟧`.
- `PowerSeries.HasNonnegCoeffs` : all coefficients of `f : ℂ⟦X⟧` are nonnegative reals.

## Main statements

- `PowerSeries.radius_le_radius_of_norm_coeff_le` : coefficientwise domination bounds radii.
- `PowerSeries.min_radius_le_radius_mul` : the radius of a product is at least the smaller radius.
- `PowerSeries.le_radius_coe_mul_inv_prod` : a polynomial divided by `∏ (1 - c X)` converges on
  every disc on which all the `1 - c X` are invertible.
- `PowerSeries.eval_ne_zero_of_lt_radius_inv` : a polynomial has no zero inside the disc of
  convergence of its inverse.
- `PowerSeries.radius_tprod_le_radius` : a factor of a convergent product of nonnegative series
  with constant term `1` has at least the radius of the product.
- `PowerSeries.eval_ne_zero_of_lt_radius_tprod_inv` : if the inverses of polynomials `P_j` with
  `P_j(0) = 1` form such a product, no `P_j` vanishes inside its disc of convergence.
- `PowerSeries.le_radius_of_differentiableOn` : the Taylor series at `0` of a function
  holomorphic on the disc of radius `R` has radius at least `R`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PowerSeries

/-- Blueprint `lemma-positivity-convergence--1`: Radius of a formal series.

The radius of convergence `R(f) ∈ ℝ≥0∞` of a formal power series `f = ∑ aₙ Tⁿ ∈ 𝕜⟦X⟧` over a
nontrivially normed field `𝕜`.

This is defined as the radius of convergence of the associated formal multilinear series
`FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ coeff n f)`, whose `n`-th coefficient is `aₙ` by
`FormalMultilinearSeries.coeff_ofScalars`. It agrees with the description in the blueprint as
the supremum of the `r ≥ 0` for which `∑ₙ ‖aₙ‖ tⁿ` converges for all `0 ≤ t < r`: by
`FormalMultilinearSeries.radius` it is the supremum of the `r ≥ 0` for which `‖aₙ‖ rⁿ` is
bounded, and boundedness of `‖aₙ‖ rⁿ` for one `r` is equivalent to summability of
`∑ₙ ‖aₙ‖ tⁿ` for all `t < r` (`FormalMultilinearSeries.summable_norm_mul_pow` and
`FormalMultilinearSeries.le_radius_of_summable_norm`). -/
noncomputable def radius {𝕜 : Type*} [NontriviallyNormedField 𝕜] (f : 𝕜⟦X⟧) : ℝ≥0∞ :=
  (FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n f).radius

/-- Blueprint `lemma-positivity-convergence--1`: Radius of a formal series.

A formal power series `f = ∑ aₙ Tⁿ ∈ ℂ⟦X⟧` has nonnegative coefficients if every `aₙ` is a
nonnegative real number. These are the series for which the coefficientwise comparison
arguments of the real-sheaves chapter apply: a coefficientwise bound between them is preserved
by products and gives a bound on the radius of convergence. -/
def HasNonnegCoeffs (f : ℂ⟦X⟧) : Prop :=
  ∀ n, coeff n f ∈ Set.range ((↑) : ℝ≥0 → ℂ)

section Radius

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Inside the radius of convergence the series of norms `∑ ‖aₙ‖ rⁿ` converges. -/
theorem summable_norm_coeff_mul_pow {f : 𝕜⟦X⟧} {r : ℝ≥0} (h : (r : ℝ≥0∞) < f.radius) :
    Summable fun n ↦ ‖coeff n f‖ * (r : ℝ) ^ n := by
  simpa [FormalMultilinearSeries.ofScalars_norm] using
    (FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n f).summable_norm_mul_pow h

/-- If the series of norms `∑ ‖aₙ‖ rⁿ` converges, then `r` is at most the radius. -/
theorem le_radius_of_summable {f : 𝕜⟦X⟧} {r : ℝ≥0}
    (h : Summable fun n ↦ ‖coeff n f‖ * (r : ℝ) ^ n) : (r : ℝ≥0∞) ≤ f.radius :=
  (FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n f).le_radius_of_summable_norm
    (by simpa [FormalMultilinearSeries.ofScalars_norm] using h)

/-- If `‖aₙ‖ rⁿ` is bounded, then `r` is at most the radius. -/
theorem le_radius_of_bound {f : 𝕜⟦X⟧} {r : ℝ≥0} (B : ℝ)
    (h : ∀ n, ‖coeff n f‖ * (r : ℝ) ^ n ≤ B) : (r : ℝ≥0∞) ≤ f.radius :=
  (FormalMultilinearSeries.ofScalars 𝕜 fun n ↦ coeff n f).le_radius_of_bound B
    (by simpa [FormalMultilinearSeries.ofScalars_norm] using h)

/-- A series whose coefficients are dominated in norm by those of `g` has at least the radius
of `g`. -/
theorem radius_le_radius_of_norm_coeff_le {f g : 𝕜⟦X⟧} (h : ∀ n, ‖coeff n f‖ ≤ ‖coeff n g‖) :
    g.radius ≤ f.radius :=
  ENNReal.le_of_forall_nnreal_lt fun _ hr ↦ le_radius_of_summable <|
    (summable_norm_coeff_mul_pow hr).of_nonneg_of_le (fun _ ↦ by positivity)
      fun n ↦ mul_le_mul_of_nonneg_right (h n) (by positivity)

/-- The radius of a product of two series is at least the smaller of their radii: inside both
discs the Cauchy product of the two absolutely convergent series converges absolutely. -/
theorem min_radius_le_radius_mul (f g : 𝕜⟦X⟧) : min f.radius g.radius ≤ (f * g).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ le_radius_of_summable ?_
  set a : ℕ → ℝ := fun n ↦ ‖coeff n f‖ * (r : ℝ) ^ n
  set b : ℕ → ℝ := fun n ↦ ‖coeff n g‖ * (r : ℝ) ^ n
  have ha : Summable fun n ↦ ‖a n‖ := by
    simpa [a, abs_of_nonneg] using summable_norm_coeff_mul_pow (hr.trans_le (min_le_left _ _))
  have hb : Summable fun n ↦ ‖b n‖ := by
    simpa [b, abs_of_nonneg] using summable_norm_coeff_mul_pow (hr.trans_le (min_le_right _ _))
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb).of_nonneg_of_le
    (fun _ ↦ by positivity) fun n ↦ ?_
  rw [coeff_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)]
  calc ‖∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff p.2 g‖ * (r : ℝ) ^ n
      ≤ (∑ p ∈ Finset.antidiagonal n, ‖coeff p.1 f‖ * ‖coeff p.2 g‖) * (r : ℝ) ^ n := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_mul_le _ _)
    _ = ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← Finset.mem_antidiagonal.1 hp, pow_add]
        ring

/-- A polynomial has infinite radius of convergence. -/
theorem radius_coe (P : Polynomial 𝕜) : (P : 𝕜⟦X⟧).radius = ⊤ :=
  ENNReal.eq_top_of_forall_nnreal_le fun _ ↦ le_radius_of_summable <|
    summable_of_ne_finset_zero (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simpa [Nat.lt_succ_iff] using hn), norm_zero, zero_mul]

/-- The inverse of `1 - c X` is the geometric series `∑ cⁿ Xⁿ`. -/
theorem inv_one_sub_C_mul_X (c : 𝕜) : (1 - C c * X : 𝕜⟦X⟧)⁻¹ = mk (c ^ ·) := by
  refine ((PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2 ?_).symm
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_mul_X, mul_comm, coeff_C_mul, coeff_mk, coeff_mk, pow_succ']
    simp

/-- The geometric series `(1 - c X)⁻¹` converges on the disc of radius `r` when `‖c‖ r < 1`. -/
theorem le_radius_inv_one_sub_C_mul_X {c : 𝕜} {r : ℝ≥0} (hr : ‖c‖ * r < 1) :
    (r : ℝ≥0∞) ≤ (1 - C c * X : 𝕜⟦X⟧)⁻¹.radius := by
  refine le_radius_of_summable ?_
  simp only [inv_one_sub_C_mul_X, coeff_mk, norm_pow, ← mul_pow]
  exact summable_geometric_of_lt_one (by positivity) hr

/-- A polynomial divided by `∏ (1 - c X)` converges on the disc of radius `r` as soon as
`‖c‖ r < 1` for all `c`. -/
theorem le_radius_coe_mul_inv_prod (P : Polynomial 𝕜) (s : Multiset 𝕜) {r : ℝ≥0}
    (hr : ∀ c ∈ s, ‖c‖ * r < 1) :
    (r : ℝ≥0∞) ≤ ((P : 𝕜⟦X⟧) * ((s.map fun c ↦ 1 - C c * X).prod)⁻¹).radius := by
  induction s using Multiset.induction_on generalizing P with
  | empty => simp [radius_coe]
  | cons c s ih =>
    have h : (P : 𝕜⟦X⟧) * ((((c ::ₘ s).map fun c ↦ 1 - C c * X).prod)⁻¹) =
        (1 - C c * X)⁻¹ * ((P : 𝕜⟦X⟧) * ((s.map fun c ↦ 1 - C c * X).prod)⁻¹) := by
      rw [Multiset.map_cons, Multiset.prod_cons, MvPowerSeries.mul_inv_rev]
      ring
    rw [h]
    refine le_trans (le_min ?_ (ih P fun c hc ↦ hr c (Multiset.mem_cons_of_mem hc)))
      (min_radius_le_radius_mul _ _)
    exact le_radius_inv_one_sub_C_mul_X (hr c (Multiset.mem_cons_self c s))

/-- A polynomial with nonzero constant term has no zero inside the disc of convergence of its
inverse: at such a zero `z` the Cauchy product of the convergent series `P (z) = ∑ pₙ zⁿ` and
`P⁻¹ (z) = ∑ bₙ zⁿ` would be the value `1` of the series `P P⁻¹ = 1`. -/
theorem eval_ne_zero_of_lt_radius_inv [CompleteSpace 𝕜] {P : Polynomial 𝕜} (hP : P.coeff 0 ≠ 0)
    {z : 𝕜} (hz : (‖z‖₊ : ℝ≥0∞) < ((P : 𝕜⟦X⟧)⁻¹).radius) : P.eval z ≠ 0 := by
  set G := (P : 𝕜⟦X⟧)⁻¹
  have hPG : (P : 𝕜⟦X⟧) * G = 1 :=
    PowerSeries.mul_inv_cancel _ (by rwa [← coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe])
  have hf : Summable fun n ↦ ‖P.coeff n * z ^ n‖ :=
    summable_of_ne_finset_zero (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul, norm_zero]
  have hg : Summable fun n ↦ ‖coeff n G * z ^ n‖ := by
    simpa [norm_mul, norm_pow] using summable_norm_coeff_mul_pow hz
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have hP : ∑' n, P.coeff n * z ^ n = P.eval z := by
    rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul], Polynomial.eval_eq_sum_range]
  have h1 : ∑' n, ∑ p ∈ Finset.antidiagonal n, P.coeff p.1 * z ^ p.1 * (coeff p.2 G * z ^ p.2)
      = 1 := by
    have h (n : ℕ) : ∑ p ∈ Finset.antidiagonal n, P.coeff p.1 * z ^ p.1 * (coeff p.2 G * z ^ p.2)
        = coeff n ((P : 𝕜⟦X⟧) * G) * z ^ n := by
      rw [coeff_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [← Finset.mem_antidiagonal.1 hp, pow_add, Polynomial.coeff_coe]
      ring
    simp_rw [h, hPG, coeff_one]
    rw [tsum_eq_single 0 fun n hn ↦ by simp [hn]]
    simp
  rw [hP, h1] at key
  exact left_ne_zero_of_mul_eq_one key

end Radius

section Nonneg

open scoped ComplexOrder PowerSeries.WithPiTopology

theorem hasNonnegCoeffs_iff {f : ℂ⟦X⟧} : f.HasNonnegCoeffs ↔ ∀ n, 0 ≤ coeff n f := by
  refine forall_congr' fun n ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact Complex.zero_le_real.2 a.2
  · obtain ⟨a, ha, h⟩ := RCLike.nonneg_iff_exists_ofReal.1 h
    exact ⟨⟨a, ha⟩, h⟩

/-- Blueprint `lemma-positivity-convergence--1`: Positive products and radii of convergence.

Let `(f_j)` be a family of series in `1 + T ℝ≥0⟦T⟧` whose product converges in the product
topology. Then every factor `f_j` has radius of convergence at least that of the product.

Indeed nonnegativity and the constant terms `1` give the coefficientwise inequality
`0 ≤ a_{j, n} ≤ A_n` between the coefficients of `f_j` and those of the product, first for the
finite partial products containing `f_j` and then, the set of such series being closed, for the
product itself. -/
theorem radius_tprod_le_radius {J : Type*} {f : J → ℂ⟦X⟧} (hf : ∀ j, (f j).HasNonnegCoeffs)
    (h1 : ∀ j, constantCoeff (f j) = 1) (hmul : Multipliable f) (j : J) :
    (∏' i, f i).radius ≤ (f j).radius := by
  classical
  simp_rw [hasNonnegCoeffs_iff] at hf
  -- the series with nonnegative coefficients dominating `f j`
  let D : Set ℂ⟦X⟧ := {g | ∀ n, coeff n (f j) ≤ coeff n g}
  have hD : IsClosed D := by
    have : D = ⋂ n, {g | coeff n (f j) ≤ coeff n g} := by ext; simp [D]
    rw [this]
    exact isClosed_iInter fun n ↦ isClosed_le continuous_const
      (WithPiTopology.continuous_coeff ℂ n)
  have hmono (g h : ℂ⟦X⟧) (hg : ∀ n, 0 ≤ coeff n g) (hh : ∀ n, 0 ≤ coeff n h)
      (hh1 : constantCoeff h = 1) : ∀ n, coeff n g ≤ coeff n (g * h) := by
    intro n
    rw [coeff_mul, ← Finset.add_sum_erase _ _
      (show ((n, 0) : ℕ × ℕ) ∈ Finset.antidiagonal n by simp)]
    simp only [coeff_zero_eq_constantCoeff_apply, hh1, mul_one, le_add_iff_nonneg_right]
    exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hg _) (hh _)
  have hnonneg (s : Finset J) : ∀ n, 0 ≤ coeff n (∏ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => intro n; rw [Finset.prod_empty, coeff_one]; split_ifs <;> simp
    | insert a s ha ih =>
      intro n
      rw [Finset.prod_insert ha, coeff_mul]
      exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hf a _) (ih _)
  have hconst (s : Finset J) : constantCoeff (∏ i ∈ s, f i) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun i _ ↦ h1 i
  have hev : ∀ᶠ s in Filter.atTop, ∏ i ∈ s, f i ∈ D := by
    filter_upwards [Filter.eventually_ge_atTop {j}] with s hs
    rw [← Finset.mul_prod_erase s f (Finset.singleton_subset_iff.1 hs)]
    exact hmono _ _ (hf j) (hnonneg _) (hconst _)
  have hmem : ∏' i, f i ∈ D := hD.mem_of_tendsto hmul.hasProd hev
  refine radius_le_radius_of_norm_coeff_le fun n ↦ ?_
  obtain ⟨a, ha, hfa⟩ := RCLike.nonneg_iff_exists_ofReal.1 (hf j n)
  obtain ⟨b, hb, hfb⟩ := RCLike.nonneg_iff_exists_ofReal.1 ((hf j n).trans (hmem n))
  have hab := hmem n
  rw [← hfa, ← hfb] at hab ⊢
  rw [RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg ha, abs_of_nonneg hb]
  exact_mod_cast hab

/-- Blueprint `lemma-positivity-convergence--1` (the "in particular" clause): Positive products
and radii of convergence.

Let `(P_j)` be polynomials with `P_j(0) = 1` whose inverses `f_j = P_j⁻¹` lie in
`1 + T ℝ≥0⟦T⟧` and have a convergent product `F = ∏ f_j`. Then no `P_j` vanishes in the open
disc of radius `R(F)`: each `P_j⁻¹` has radius at least `R(F)` by `radius_tprod_le_radius`, and
a polynomial has no zero inside the disc of convergence of its inverse
(`eval_ne_zero_of_lt_radius_inv`). -/
theorem eval_ne_zero_of_lt_radius_tprod_inv {J : Type*} {P : J → Polynomial ℂ}
    (hP : ∀ j, (P j).coeff 0 = 1) (hf : ∀ j, ((P j : ℂ⟦X⟧)⁻¹).HasNonnegCoeffs)
    (hmul : Multipliable fun j ↦ (P j : ℂ⟦X⟧)⁻¹) (j : J) {z : ℂ}
    (hz : (‖z‖₊ : ℝ≥0∞) < (∏' i, (P i : ℂ⟦X⟧)⁻¹).radius) : (P j).eval z ≠ 0 :=
  eval_ne_zero_of_lt_radius_inv (by simp [hP]) <| hz.trans_le <|
    radius_tprod_le_radius hf (fun i ↦ by
      rw [constantCoeff_inv, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP,
        inv_one]) hmul j

/-- Blueprint `lemma-positivity-convergence--1` (holomorphic hypothesis): Positive products and
radii of convergence.

If `F ∈ ℂ⟦X⟧` is the Taylor series at `0` of a function `g` holomorphic on the open disc of
radius `R`, then `F` has radius of convergence at least `R`: on every closed disc of radius
`r < R` the Cauchy integral formula expands `g` into a power series, which agrees with the
Taylor series of `g` by uniqueness of power series expansions. -/
theorem le_radius_of_differentiableOn {g : ℂ → ℂ} {R : ℝ≥0∞} {F : ℂ⟦X⟧}
    (hg : DifferentiableOn ℂ g (Metric.eball 0 R))
    (hF : ∀ n, coeff n F = iteratedDeriv n g 0 / n.factorial) : R ≤ F.radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr hrR ↦ ?_
  have hp := (hg.mono fun z hz ↦ mem_eball_zero_iff.2 <| lt_of_le_of_lt (by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hz) hrR).hasFPowerSeriesOnBall hr
  have h := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have hrad : F.radius = (cauchyPowerSeries g 0 r).radius := by
    rw [radius, h]
    simp_rw [hF]
  exact hrad ▸ hp.r_le

/-- Blueprint `lemma-positivity-convergence--1`: Positive products and radii of convergence.

Let `(f_j)` be a family of series in `1 + T ℝ≥0⟦T⟧` whose product converges in the product
topology. If the product is the Taylor series at `0` of a function `g` holomorphic on the open
disc of radius `R`, then every factor `f_j` has radius of convergence at least `R`. -/
theorem le_radius_of_differentiableOn_tprod {J : Type*} {f : J → ℂ⟦X⟧}
    (hf : ∀ j, (f j).HasNonnegCoeffs) (h1 : ∀ j, constantCoeff (f j) = 1) (hmul : Multipliable f)
    {g : ℂ → ℂ} {R : ℝ≥0∞} (hg : DifferentiableOn ℂ g (Metric.eball 0 R))
    (hF : ∀ n, coeff n (∏' i, f i) = iteratedDeriv n g 0 / n.factorial) (j : J) :
    R ≤ (f j).radius :=
  (le_radius_of_differentiableOn hg hF).trans (radius_tprod_le_radius hf h1 hmul j)

/-- Blueprint `lemma-positivity-convergence--1` (the "in particular" clause): Positive products
and radii of convergence.

Let `(P_j)` be polynomials with `P_j(0) = 1` whose inverses `f_j = P_j⁻¹` lie in
`1 + T ℝ≥0⟦T⟧` and have a convergent product `F = ∏ f_j`. If `F` is the Taylor series at `0` of
a function holomorphic on the open disc of radius `R`, then no `P_j` vanishes in that disc. -/
theorem eval_ne_zero_of_differentiableOn_tprod_inv {J : Type*} {P : J → Polynomial ℂ}
    (hP : ∀ j, (P j).coeff 0 = 1) (hf : ∀ j, ((P j : ℂ⟦X⟧)⁻¹).HasNonnegCoeffs)
    (hmul : Multipliable fun j ↦ (P j : ℂ⟦X⟧)⁻¹) {g : ℂ → ℂ} {R : ℝ≥0∞}
    (hg : DifferentiableOn ℂ g (Metric.eball 0 R))
    (hF : ∀ n, coeff n (∏' i, (P i : ℂ⟦X⟧)⁻¹) = iteratedDeriv n g 0 / n.factorial) (j : J)
    {z : ℂ} (hz : ‖z‖ₑ < R) : (P j).eval z ≠ 0 :=
  eval_ne_zero_of_lt_radius_tprod_inv hP hf hmul j <|
    (enorm_eq_nnnorm z ▸ hz).trans_le (le_radius_of_differentiableOn hg hF)


end Nonneg

section Pole

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- If `f Q = P` for polynomials `P` and `Q`, then inside the disc of convergence of `f` the
sum of `f` at `z` times `Q (z)` is `P (z)`: the Cauchy product of the two absolutely convergent
series. -/
theorem tsum_mul_eval_eq_eval_of_mul_eq {f : 𝕜⟦X⟧} {P Q : Polynomial 𝕜}
    (h : f * (Q : 𝕜⟦X⟧) = P) {z : 𝕜} (hz : (‖z‖₊ : ℝ≥0∞) < f.radius) :
    (∑' n, coeff n f * z ^ n) * Q.eval z = P.eval z := by
  have hQ : Summable fun n ↦ ‖Q.coeff n * z ^ n‖ :=
    summable_of_ne_finset_zero (s := Finset.range (Q.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul, norm_zero]
  have hf : Summable fun n ↦ ‖coeff n f * z ^ n‖ := by
    simpa [norm_mul, norm_pow] using summable_norm_coeff_mul_pow hz
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hQ
  have hQe : ∑' n, Q.coeff n * z ^ n = Q.eval z := by
    rw [tsum_eq_sum (s := Finset.range (Q.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul], Polynomial.eval_eq_sum_range]
  have h1 (n : ℕ) : ∑ p ∈ Finset.antidiagonal n, coeff p.1 f * z ^ p.1 * (Q.coeff p.2 * z ^ p.2)
      = P.coeff n * z ^ n := by
    rw [← Polynomial.coeff_coe P, ← h, coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← Finset.mem_antidiagonal.1 hp, pow_add, Polynomial.coeff_coe]
    ring
  simp_rw [h1] at key
  rw [← hQe, key, tsum_eq_sum (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul], Polynomial.eval_eq_sum_range]

/-- **A pole bounds the radius.** If `f Q = P` for polynomials `P` and `Q` and `z` is a zero of
`Q` which is not a zero of `P`, then the radius of convergence of `f` is at most `‖z‖`. -/
theorem radius_le_of_mul_eq {f : 𝕜⟦X⟧} {P Q : Polynomial 𝕜} (h : f * (Q : 𝕜⟦X⟧) = P) {z : 𝕜}
    (hQ : Q.eval z = 0) (hP : P.eval z ≠ 0) : f.radius ≤ ‖z‖₊ := by
  by_contra hz
  rw [not_le] at hz
  have := tsum_mul_eval_eq_eval_of_mul_eq h hz
  rw [hQ, mul_zero] at this
  exact hP this.symm


/-- **A rational function which is not a polynomial has a pole.** If `f D = N` for polynomials
`N` and `D ≠ 0` over `ℂ`, every zero of `D` has absolute value at most `R`, and `f` is not
everywhere convergent, then the radius of convergence of `f` is at most `R`: in lowest terms
`f = N₀ / D₀` the denominator `D₀` divides `D` and is not constant, and a zero of `D₀` is not a
zero of `N₀`. -/
theorem radius_le_of_mul_coe_eq {f : ℂ⟦X⟧} {N D : Polynomial ℂ} (h : f * D = N) (hD : D ≠ 0)
    {R : ℝ≥0} (hroots : ∀ z, D.eval z = 0 → ‖z‖₊ ≤ R) (hf : f.radius ≠ ⊤) : f.radius ≤ R := by
  classical
  set g := GCDMonoid.gcd N D
  have hg : g ≠ 0 := gcd_ne_zero_of_right hD
  set N₀ := N / g
  set D₀ := D / g
  have hN : g * N₀ = N := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hD' : g * D₀ = D := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right _ _)
  have hcop : IsCoprime N₀ D₀ := isCoprime_div_gcd_div_gcd hD
  have h₀ : f * D₀ = N₀ := by
    have hg' : (g : ℂ⟦X⟧) ≠ 0 := by
      rw [Ne, Polynomial.coe_eq_zero_iff]
      exact hg
    refine sub_eq_zero.1 ((mul_eq_zero.1 ?_).resolve_left hg')
    rw [mul_sub, ← mul_assoc, mul_comm (g : ℂ⟦X⟧) f, mul_assoc, ← Polynomial.coe_mul, hD',
      ← Polynomial.coe_mul, hN, h, sub_self]
  by_cases hdeg : D₀.degree = 0
  · exfalso
    have hc := Polynomial.eq_C_of_degree_eq_zero hdeg
    set c := D₀.coeff 0
    have hc0 : c ≠ 0 := fun h0 ↦ hD (by rw [<- hD', hc, h0, map_zero, mul_zero])
    refine hf ?_
    have hf' : f = ((N₀ * Polynomial.C c⁻¹ : Polynomial ℂ) : ℂ⟦X⟧) := by
      rw [Polynomial.coe_mul, <- h₀, hc, Polynomial.coe_C, Polynomial.coe_C, mul_assoc, <- map_mul,
        mul_inv_cancel₀ hc0, map_one, mul_one]
    rw [hf', radius_coe]
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root D₀ hdeg
    have hNz : N₀.eval z ≠ 0 := by
      obtain ⟨a, b, hab⟩ := hcop
      intro h0
      have := congrArg (Polynomial.eval z) hab
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h0, hz.eq_zero,
        mul_zero, mul_zero, add_zero, Polynomial.eval_one] at this
      exact zero_ne_one this
    refine (radius_le_of_mul_eq h₀ hz.eq_zero hNz).trans ?_
    exact_mod_cast hroots z (by rw [← hD', Polynomial.eval_mul, hz.eq_zero, mul_zero])
end Pole

section LogDerivative

/-- **The solution of `f' = g f` converges where `g` does.** If `f' = g f`, then the radius of
convergence of `f` is at least that of `g`: writing `mₙ = ‖fₙ‖ rⁿ` for `r` inside the disc of
`g`, the recursion `(n + 1) f_{n + 1} = ∑_{i + j = n} gᵢ fⱼ` gives
`(n + 1) m_{n + 1} ≤ r C (m₀ + ⋯ + mₙ)` with `C = ∑ ‖gᵢ‖ rⁱ`, so the partial sums of the `mₙ`
grow more slowly than any exponential `(1 + ε)ⁿ`. -/
theorem radius_le_radius_of_derivative_eq_mul {f g : ℂ⟦X⟧} (h : derivative (R := ℂ) f = g * f) :
    g.radius ≤ f.radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ENNReal.le_of_forall_nnreal_lt fun ρ hρ ↦ ?_
  have hρr : (ρ : ℝ) < r := by exact_mod_cast hρ
  rcases eq_or_ne ρ 0 with rfl | hρ0
  · simp
  have hρ0' : (0 : ℝ) < ρ := by positivity
  have hr0 : (0 : ℝ) < r := hρ0'.trans hρr
  set C := ∑' n, ‖coeff n g‖ * (r : ℝ) ^ n
  have hgs := summable_norm_coeff_mul_pow hr
  have hC : ∀ s : Finset ℕ, ∑ i ∈ s, ‖coeff i g‖ * (r : ℝ) ^ i ≤ C := fun s ↦
    hgs.sum_le_tsum s fun _ _ ↦ by positivity
  have hC0 : 0 ≤ C := tsum_nonneg fun _ ↦ by positivity
  set m : ℕ → ℝ := fun n ↦ ‖coeff n f‖ * (r : ℝ) ^ n
  set M : ℕ → ℝ := fun n ↦ ∑ j ∈ Finset.range (n + 1), m j
  have hm0 : ∀ n, 0 ≤ m n := fun n ↦ by positivity
  have hM0 : ∀ n, 0 ≤ M n := fun n ↦ Finset.sum_nonneg fun j _ ↦ hm0 j
  -- the recursion
  have hrec : ∀ n : ℕ, ((n : ℝ) + 1) * m (n + 1) ≤ r * C * M n := by
    intro n
    have hc := congrArg (coeff n) h
    rw [coeff_derivative, coeff_mul] at hc
    have h1 : ((n : ℝ) + 1) * ‖coeff (n + 1) f‖ ≤
        ∑ p ∈ Finset.antidiagonal n, ‖coeff p.1 g‖ * ‖coeff p.2 f‖ := by
      calc ((n : ℝ) + 1) * ‖coeff (n + 1) f‖ = ‖coeff (n + 1) f * ((n : ℂ) + 1)‖ := by
            rw [norm_mul, mul_comm]
            congr 1
            exact_mod_cast (Complex.norm_natCast (n + 1)).symm
        _ = ‖∑ p ∈ Finset.antidiagonal n, coeff p.1 g * coeff p.2 f‖ := by rw [hc]
        _ ≤ _ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_mul_le _ _)
    calc ((n : ℝ) + 1) * m (n + 1)
        = r * (((n : ℝ) + 1) * ‖coeff (n + 1) f‖ * (r : ℝ) ^ n) := by
          simp only [m]; ring
      _ ≤ r * ((∑ p ∈ Finset.antidiagonal n, ‖coeff p.1 g‖ * ‖coeff p.2 f‖) * (r : ℝ) ^ n) := by
          gcongr
      _ = r * ∑ p ∈ Finset.antidiagonal n, (‖coeff p.1 g‖ * (r : ℝ) ^ p.1) * m p.2 := by
          rw [Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun p hp ↦ ?_
          rw [← Finset.mem_antidiagonal.1 hp, pow_add]
          simp only [m]
          ring
      _ ≤ r * ∑ p ∈ Finset.antidiagonal n, (‖coeff p.1 g‖ * (r : ℝ) ^ p.1) * M n := by
          gcongr with p hp
          exact Finset.single_le_sum (fun j _ ↦ hm0 j)
            (Finset.mem_range.2 (by have := Finset.mem_antidiagonal.1 hp; omega))
      _ = r * (∑ i ∈ Finset.range (n + 1), ‖coeff i g‖ * (r : ℝ) ^ i) * M n := by
          rw [← Finset.sum_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          ring
      _ ≤ r * C * M n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC _) hr0.le) (hM0 n)
  -- the partial sums grow subexponentially
  set ε : ℝ := r / ρ - 1
  have hε : 0 < ε := by
    simp only [ε, sub_pos]
    rw [one_lt_div hρ0']
    exact hρr
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r * C ≤ ε * ((N : ℝ) + 1) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (r * C / ε)
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ hε] at hN
    nlinarith
  have hstep : ∀ n, N ≤ n → M (n + 1) ≤ (1 + ε) * M n := by
    intro n hn
    have h1 := hrec n
    have h2 : r * C ≤ ε * ((n : ℝ) + 1) := hN.trans (by gcongr)
    have h3 : ((n : ℝ) + 1) * m (n + 1) ≤ ((n : ℝ) + 1) * (ε * M n) := by
      nlinarith [hM0 n]
    have h4 : m (n + 1) ≤ ε * M n := le_of_mul_le_mul_left h3 (by positivity)
    simp only [M, Finset.sum_range_succ] at h4 ⊢
    linarith
  have hbound : ∀ n, M n ≤ M N * (1 + ε) ^ n := by
    intro n
    induction n with
    | zero =>
      have : M 0 ≤ M N := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by omega)) fun j _ _ ↦ hm0 j
      simpa using this
    | succ n ih =>
      rcases lt_or_ge n N with hn | hn
      · have : M (n + 1) ≤ M N := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) fun j _ _ ↦ hm0 j
        exact this.trans (le_mul_of_one_le_right (hM0 N) (one_le_pow₀ (by linarith)))
      · calc M (n + 1) ≤ (1 + ε) * M n := hstep n hn
          _ ≤ (1 + ε) * (M N * (1 + ε) ^ n) := by gcongr
          _ = M N * (1 + ε) ^ (n + 1) := by ring
  have hρε : (ρ : ℝ) = r / (1 + ε) := by
    simp only [ε, add_sub_cancel]
    field_simp
  refine le_radius_of_bound (M N) fun n ↦ ?_
  have hmn : m n ≤ M n := Finset.single_le_sum (fun j _ ↦ hm0 j) (Finset.self_mem_range_succ n)
  calc ‖coeff n f‖ * (ρ : ℝ) ^ n = m n / (1 + ε) ^ n := by
        rw [hρε, div_pow]
        simp only [m]
        ring
    _ ≤ M n / (1 + ε) ^ n := by gcongr
    _ ≤ M N := by
        rw [div_le_iff₀ (by positivity)]
        exact hbound n

end LogDerivative

section NonnegRecursion

open scoped ComplexOrder

/-- If `X G' = S G` with `S` having nonnegative coefficients and no constant term, and `G` has a
nonnegative constant coefficient, then all the coefficients of `G` are nonnegative: the
recursion `n gₙ = ∑_{i + j = n, i ≥ 1} sᵢ gⱼ` preserves nonnegativity. -/
theorem coeff_nonneg_of_X_mul_derivative_eq {G S : ℂ⟦X⟧} (h : X * derivative (R := ℂ) G = S * G)
    (hS : ∀ n, 0 ≤ coeff n S) (hS0 : coeff 0 S = 0) (hG0 : 0 ≤ coeff 0 G) (k : ℕ) :
    0 ≤ coeff k G := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | k
  · exact hG0
  · have hc := congrArg (coeff (k + 1)) h
    rw [coeff_succ_X_mul, coeff_derivative, coeff_mul] at hc
    have hsum : 0 ≤ ∑ p ∈ Finset.antidiagonal (k + 1), coeff p.1 S * coeff p.2 G := by
      refine Finset.sum_nonneg fun p hp ↦ ?_
      rcases eq_or_ne p.1 0 with h0 | h0
      · simp [h0, hS0]
      · have hi : p.2 < k + 1 := by
          have := Finset.mem_antidiagonal.1 hp
          omega
        exact mul_nonneg (hS _) (ih p.2 hi)
    have hk : coeff (k + 1) G = (((k + 1 : ℕ) : ℝ)⁻¹ : ℝ) *
        ∑ p ∈ Finset.antidiagonal (k + 1), coeff p.1 S * coeff p.2 G := by
      rw [← hc]
      push_cast
      field_simp
    rw [hk]
    exact mul_nonneg (Complex.zero_le_real.2 (by positivity)) hsum

end NonnegRecursion

end PowerSeries

namespace FormalMultilinearSeries

/-- The radius of convergence of a real scalar series is that of the same series over `ℂ`. -/
theorem radius_ofScalars_real_eq (c : ℕ → ℝ) :
    (ofScalars ℝ c).radius = PowerSeries.radius (PowerSeries.mk fun n ↦ (c n : ℂ)) := by
  simp only [PowerSeries.radius, FormalMultilinearSeries.radius, ofScalars_norm,
    PowerSeries.coeff_mk, Complex.norm_real]

end FormalMultilinearSeries
