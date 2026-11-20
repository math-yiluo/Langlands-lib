import Langlands.Representation.Archimedean.ComplexSwapJacquetProof
import Langlands.Representation.Archimedean.ComplexSwapJacquetNonvanishing
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction

/-! # The complex adjacent-swap integral for strictly decreasing exponents -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator
open MeasureTheory Filter Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.LocalFactor.Archimedean

variable {n : ℕ}

private theorem rpow_neg_le_of_le_twice {a b p : ℝ}
    (hb : 0 < b) (hab : b ≤ 2 * a) (hp : 0 ≤ p) :
    a ^ (-p) ≤ (2 : ℝ) ^ p * b ^ (-p) := by
  calc
    a ^ (-p) ≤ (b / 2) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr hp)
    _ = _ := by
      rw [Real.div_rpow hb.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]

private theorem integrable_of_chart_bound {φ : ℂ → ℂ} {p C : ℝ}
    (hp : 2 < p) (hφ : Continuous φ) (hC : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖) ^ (-p)) :
    Integrable φ :=
  ((integrable_one_add_norm (E := ℂ) (μ := volume) (r := p)
    (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hp)).const_mul C).mono'
      hφ.aestronglyMeasurable (Eventually.of_forall hC)

private theorem exists_bound_chart_of_strict (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (hre : 0 < (d.exponent - e.exponent).re)
    {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n (pre ++ d :: e :: post)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖h (chart i j hj z)‖ ≤
        C * (1 + ‖z‖) ^ (-(2 + 2 * (d.exponent - e.exponent).re)) := by
  let p : ℝ := 2 + 2 * (d.exponent - e.exponent).re
  have hp : 0 ≤ p := by
    change 0 ≤ 2 + 2 * (d.exponent - e.exponent).re
    linarith
  obtain ⟨M, hM₀, hM⟩ := exists_bound_ball (contDiff_apply_lowerChart hh.1 i j hj).continuous
  obtain ⟨M', hM'₀, hM'⟩ := exists_bound_ball (contDiff_apply_chart hh.1 i j hj).continuous
  refine ⟨(M + M') * (2 : ℝ) ^ p, by positivity, fun z => ?_⟩
  change ‖h (chart i j hj z)‖ ≤ (M + M') * (2 : ℝ) ^ p * (1 + ‖z‖) ^ (-p)
  rcases le_total ‖z‖ 1 with hz | hz
  · have hpow := rpow_neg_le_of_le_twice (a := 1) (b := 1 + ‖z‖)
        (by positivity) (by linarith) hp
    rw [Real.one_rpow] at hpow
    calc
      ‖h (chart i j hj z)‖ ≤ M' := hM' z hz
      _ ≤ (M + M') * 1 := by linarith
      _ ≤ (M + M') * ((2 : ℝ) ^ p * (1 + ‖z‖) ^ (-p)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  · have hpos : 0 < ‖z‖ := by linarith
    have hz₀ : z ≠ 0 := norm_pos_iff.mp hpos
    have hpow := rpow_neg_le_of_le_twice (a := ‖z‖) (by positivity : 0 < 1 + ‖z‖)
      (by linarith) hp
    have hzinv : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hz
    rw [apply_chart_eq hh i j hj z hz₀, norm_mul,
      norm_principalSeriesCharacter_chartTorus pre post d e i j hi hj]
    change ‖z‖ ^ (-2 - 2 * (d.exponent - e.exponent).re) * _ ≤ _
    rw [show -2 - 2 * (d.exponent - e.exponent).re = -p by dsimp [p]; ring]
    calc
      _ ≤ ‖z‖ ^ (-p) * M := mul_le_mul_of_nonneg_left (hM z⁻¹ hzinv) (by positivity)
      _ ≤ ((2 : ℝ) ^ p * (1 + ‖z‖) ^ (-p)) * (M + M') :=
        mul_le_mul hpow (by linarith) hM₀ (by positivity)
      _ = _ := by ring

/-- In the strict convergence chamber the adjacent-swap chart integral is absolutely
convergent on every smooth vector of the source standard module. -/
theorem integrable_chart_of_strict (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (hre : 0 < (d.exponent - e.exponent).re)
    {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n (pre ++ d :: e :: post)) :
    Integrable fun z => h (chart i j hj z) := by
  obtain ⟨C, _, hC⟩ := exists_bound_chart_of_strict pre post d e i j hi hj hre hh
  exact integrable_of_chart_bound (by linarith) (contDiff_apply_chart hh.1 i j hj).continuous hC

/-- The ordinary rank-one integral evaluated at the identity, viewed as a linear
functional on the compact-finite source of a strict adjacent swap. -/
def strictSwapIntegral (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
    (i j : Fin n) (hi : (i : ℕ) = pre.length) (hj : (j : ℕ) = i + 1)
    (hre : 0 < (d.exponent - e.exponent).re) : KFs n (pre ++ d :: e :: post) →ₗ[ℂ] ℂ where
  toFun f := ∫ z, (f : Langlands.GeneralLinear n ℂ → ℂ) (chart i j hj z)
  map_add' f g :=
    integral_add (integrable_chart_of_strict pre post d e i j hi hj hre (mem_of_mem_kFs f.2))
      (integrable_chart_of_strict pre post d e i j hi hj hre (mem_of_mem_kFs g.2))
  map_smul' c f := integral_const_mul c (fun z => f.val (chart i j hj z))

private theorem integral_radial_derivative {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hφint : Integrable φ) {p C : ℝ} (hp : 2 < p) (hC₀ : 0 ≤ C)
    (hC : ∀ z, ‖fderiv ℝ φ z z‖ ≤ C * (1 + ‖z‖) ^ (-p)) :
    (∫ z, fderiv ℝ φ z z) = -2 * ∫ z, φ z := by
  have hd := hφ.differentiable one_ne_zero
  have hfc := hφ.continuous_fderiv one_ne_zero
  have hs : Metric.ball (1 : ℝ) (1 / 2) ∈ 𝓝 (1 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have hbound : ∀ z : ℂ, ∀ r ∈ Metric.ball (1 : ℝ) (1 / 2),
      ‖fderiv ℝ φ (r • z) z‖ ≤ (2 * C * (2 : ℝ) ^ p) * (1 + ‖z‖) ^ (-p) := by
    intro z r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    have hr₀ : 0 < r := by linarith
    have hr₁ : 1 ≤ 2 * r := by linarith
    have hlinear : fderiv ℝ φ (r • z) z = r⁻¹ • fderiv ℝ φ (r • z) (r • z) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ hr₀.ne', one_smul]
    have hscaled := hC (r • z)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr₀] at hscaled
    have hmean : 1 + ‖z‖ ≤ 2 * (1 + r * ‖z‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hr₁ (norm_nonneg z)]
    have hpow := rpow_neg_le_of_le_twice (p := p) (by positivity : 0 < 1 + ‖z‖)
      hmean (by linarith)
    have hinv : r⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
    rw [hlinear, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr₀)]
    calc
      _ ≤ 2 * (C * (1 + r * ‖z‖) ^ (-p)) :=
        mul_le_mul hinv hscaled (norm_nonneg _) (by norm_num)
      _ ≤ 2 * (C * ((2 : ℝ) ^ p * (1 + ‖z‖) ^ (-p))) := by gcongr
      _ = _ := by ring
  have hderiv : ∀ z : ℂ, ∀ r ∈ Metric.ball (1 : ℝ) (1 / 2),
      HasDerivAt (fun r : ℝ => φ (r • z)) (fderiv ℝ φ (r • z) z) r := by
    intro z r _
    have h := (hd (r • z)).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).smul_const z)
    rw [one_smul] at h
    exact h
  have hmajorant := (integrable_one_add_norm (E := ℂ) (μ := volume) (r := p)
    (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using hp)).const_mul
      (2 * C * (2 : ℝ) ^ p)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (r : ℝ) (z : ℂ) => φ (r • z))
    (F' := fun (r : ℝ) (z : ℂ) => fderiv ℝ φ (r • z) z) hs
    (Eventually.of_forall fun r => (hφ.continuous.comp (continuous_const_smul r)).aestronglyMeasurable)
    (by simpa only [one_smul] using hφint)
    (((hfc.comp (continuous_const_smul (1 : ℝ))).clm_apply continuous_id).aestronglyMeasurable)
    (Eventually.of_forall hbound) hmajorant (Eventually.of_forall hderiv)
  have hscale : (fun r : ℝ => ∫ z, φ (r • z)) =ᶠ[𝓝 (1 : ℝ)]
      fun r : ℝ => ((r ^ 2)⁻¹ : ℝ) • ∫ z, φ z := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with r hr
    rw [Measure.integral_comp_smul_of_nonneg volume φ r (hR := le_of_lt hr),
      Complex.finrank_real_complex]
  have hderiv_scale : HasDerivAt (fun r : ℝ => ((r ^ 2)⁻¹ : ℝ) • ∫ z, φ z)
      ((-2 : ℝ) • ∫ z, φ z) 1 := by
    have h := ((hasDerivAt_pow 2 (1 : ℝ)).inv (by norm_num)).smul_const (∫ z, φ z)
    convert h using 2
    norm_num
  have h := hmain.2.unique (hderiv_scale.congr_of_eventuallyEq hscale)
  simpa only [one_smul, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_ofNat] using h

section AdjacentSwap

variable (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
  (hn : (pre ++ d :: e :: post).length = n)
  (i j : Fin n) (hi : (i : ℕ) = pre.length) (hj : (j : ℕ) = i + 1)
  (hre : 0 < (d.exponent - e.exponent).re)

local notation "ds" => (pre ++ d :: e :: post)
local notation "es" => (pre ++ e :: d :: post)

include hi hj in
private theorem kappa_swap_difference :
    kappa ds hn i 1 - kappa ds hn j 1 - 2 = 2 * (d.exponent - e.exponent) := by
  have hdi : (ds).get (Fin.cast hn.symm i) = d :=
    getElem_append_cons_cons_left pre post d e i hi _
  have hej : (ds).get (Fin.cast hn.symm j) = e :=
    getElem_append_cons_cons_right pre post d e j (by omega) _
  rw [kappa_one, kappa_one, hdi, hej, hj]
  push_cast
  ring

/-- The regularized functional at `c = 1` is the ordinary integral times twice
the adjacent exponent difference in the strict convergence chamber. -/
theorem functional_one_eq_strictSwapIntegral (f : KFs n ds) :
    functional (chartLieFacts ds hn i j hj) (chartDecay pre post d e i j hi hj hre.le) 1 f =
      (2 * (d.exponent - e.exponent)) * strictSwapIntegral pre post d e i j hi hj hre f := by
  let φ : ℂ → ℂ := fun z => f.val (chart i j hj z)
  let p : ℝ := 2 + 2 * (d.exponent - e.exponent).re
  have hp : 2 < p := by
    change 2 < 2 + 2 * (d.exponent - e.exponent).re
    linarith
  have hf := mem_of_mem_kFs f.2
  have hφ : ContDiff ℝ 1 φ := contDiff_one_chart (i := i) (j := j) (hj := hj) hf
  have hφint : Integrable φ := integrable_chart_of_strict pre post d e i j hi hj hre hf
  let Df := rightDerivative (matrixModel ℂ n) (Matrix.single j j 1) f.val
  have hDf : Df ∈ complexStandardModule n ds :=
    rightDerivative_mem_principalSeries _ hf _
  have hdiag (z : ℂ) : Df (chart i j hj z) =
      kappa ds hn i 1 * φ z + fderiv ℝ φ z z := by
    have h := (chartLieFacts ds hn i j hj).diag_j _ hf 1 z
    rw [one_mul] at h
    exact h
  obtain ⟨C, hC₀, hC⟩ := exists_bound_chart_of_strict pre post d e i j hi hj hre hf
  obtain ⟨C', hC'₀, hC'⟩ := exists_bound_chart_of_strict pre post d e i j hi hj hre hDf
  have hDbound (z : ℂ) : ‖fderiv ℝ φ z z‖ ≤
      (C' + ‖kappa ds hn i 1‖ * C) * (1 + ‖z‖) ^ (-p) := by
    have hsub : fderiv ℝ φ z z = Df (chart i j hj z) - kappa ds hn i 1 * φ z := by
      rw [hdiag]
      ring
    rw [hsub]
    calc
      _ ≤ ‖Df (chart i j hj z)‖ + ‖kappa ds hn i 1 * φ z‖ := norm_sub_le _ _
      _ ≤ C' * (1 + ‖z‖) ^ (-p) +
          ‖kappa ds hn i 1‖ * (C * (1 + ‖z‖) ^ (-p)) := by
        rw [norm_mul]
        exact add_le_add (hC' z) (mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _))
      _ = _ := by ring
  have hDint : Integrable (fun z => fderiv ℝ φ z z) :=
    integrable_of_chart_bound hp ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_id)
      hDbound
  have heuler := integral_radial_derivative hφ hφint hp (by positivity) hDbound
  have hpt (z : ℂ) : integrand ds hn i j hj 1 f.val z =
      (kappa ds hn i 1 - kappa ds hn j 1) * φ z + fderiv ℝ φ z z := by
    change Df (chart i j hj z) - kappa ds hn j 1 * φ z = _
    rw [hdiag]
    ring
  rw [functional_apply, show (fun z => integrand ds hn i j hj 1 f.val z) = _ from funext hpt,
    integral_add (hφint.const_mul _) hDint, integral_const_mul, heuler]
  change _ = (2 * (d.exponent - e.exponent)) * (∫ z, φ z)
  rw [← kappa_swap_difference pre post d e hn i j hi hj]
  ring

private theorem functional_one_isJacquet :
    IsComplexJacquetFunctional n (complexStandardLie n ds)
      (functional (chartLieFacts ds hn i j hj) (chartDecay pre post d e i j hi hj hre.le) 1)
      (ComplexPermutation.listExponent n es ((ComplexPermutation.length_swap pre post d e).trans hn))
      (ComplexPermutation.listWeight n es ((ComplexPermutation.length_swap pre post d e).trans hn)) := by
  have hswap : ComplexPermutation.swapPerm pre post d e hn = Equiv.swap i j := by
    have hz : (⟨pre.length, by rw [← hn]; simp⟩ : Fin n) = i := Fin.ext hi.symm
    have ho : (⟨pre.length + 1, by rw [← hn]; simp⟩ : Fin n) = j := Fin.ext (by
      change pre.length + 1 = (j : ℕ)
      omega)
    rw [ComplexPermutation.swapPerm, hz, ho]
  have getSwap (k : Fin n) :
      (es).get (Fin.cast ((ComplexPermutation.length_swap pre post d e).trans hn).symm k) =
        (ds).get (Fin.cast hn.symm (Equiv.swap i j k)) := by
    simpa only [hswap, Equiv.symm_swap] using
      (ComplexPermutation.get_swap pre post d e hn k).symm
  apply isComplexJacquetFunctional_functional
  · intro k hki hkj
    rw [ComplexPermutation.listExponent, getSwap, Equiv.swap_apply_of_ne_of_ne hki hkj, kappa_one]
  · rw [ComplexPermutation.listExponent, getSwap, Equiv.swap_apply_left, kappa_one, hj]
    push_cast
    ring
  · rw [ComplexPermutation.listExponent, getSwap, Equiv.swap_apply_right, kappa_one, hj]
    push_cast
    ring
  · intro k hki hkj
    rw [ComplexPermutation.listWeight, getSwap, Equiv.swap_apply_of_ne_of_ne hki hkj, kappa_I]
  · rw [ComplexPermutation.listWeight, getSwap, Equiv.swap_apply_left, kappa_I]
  · rw [ComplexPermutation.listWeight, getSwap, Equiv.swap_apply_right, kappa_I]

/-- The ordinary strict adjacent-swap integral has the Jacquet character of the
standard module with the two adjacent inducing characters exchanged. -/
theorem strictSwapIntegral_isJacquet :
    IsComplexJacquetFunctional n (complexStandardLie n ds)
      (strictSwapIntegral pre post d e i j hi hj hre)
      (ComplexPermutation.listExponent n es ((ComplexPermutation.length_swap pre post d e).trans hn))
      (ComplexPermutation.listWeight n es ((ComplexPermutation.length_swap pre post d e).trans hn)) := by
  have hdiff : d.exponent - e.exponent ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl _ hre
  have hc := mul_ne_zero (two_ne_zero (α := ℂ)) hdiff
  let L := functional (chartLieFacts ds hn i j hj) (chartDecay pre post d e i j hi hj hre.le) 1
  let ℓ := strictSwapIntegral pre post d e i j hi hj hre
  have hscale : L = (2 * (d.exponent - e.exponent)) • ℓ := LinearMap.ext
    (functional_one_eq_strictSwapIntegral pre post d e hn i j hi hj hre)
  have hJ := functional_one_isJacquet pre post d e hn i j hi hj hre
  change IsComplexJacquetFunctional n (complexStandardLie n ds) L _ _ at hJ
  rw [hscale] at hJ
  refine ⟨fun X hX f => ?_, fun k f => ?_⟩
  · have h := hJ.1 X hX f
    change (2 * (d.exponent - e.exponent)) * ℓ _ = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hc
  · have h := hJ.2 k f
    change (_ * ℓ _ = _ * (_ * ℓ f)) ∧ (_ * ℓ _ = _ * (_ * ℓ f)) at h
    exact ⟨mul_left_cancel₀ hc (h.1.trans (mul_left_comm _ _ _)),
      mul_left_cancel₀ hc (h.2.trans (mul_left_comm _ _ _))⟩

/-- The ordinary strict adjacent-swap integral is nonzero. The right translate
of the standard nonvanishing vector by the adjacent permutation gives a radial
integrand with an explicitly nonzero integral. -/
theorem strictSwapIntegral_ne_zero :
    strictSwapIntegral pre post d e i j hi hj hre ≠ 0 := by
  let s : Langlands.GeneralLinear n ℂ := Matrix.GeneralLinearGroup.swap ℂ i j
  let f₀ : Langlands.GeneralLinear n ℂ → ℂ :=
    fun g => nzFunction n ds (g : Matrix (Fin n) (Fin n) ℂ)
  let f := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) s f₀
  have hf : f ∈ KFs n ds :=
    rightTranslation_mem_kFiniteFunctions_complexStandardModule n _
      (nzFunction_mem_kFiniteFunctions _) (swap_mem_unitaryCompact i j)
  let σ := nzExponent n ds j -
    (((nzWeight ds j).toNat : ℂ) + ((-nzWeight ds j).toNat : ℂ)) / 2
  have hσ : σ = -1 - (d.exponent - e.exponent) -
      ((((e.weight - d.weight).natAbs : ℝ) / 2 : ℝ) : ℂ) := by
    have hjval : (j : ℕ) = pre.length + 1 := by omega
    have hweight : (((e.weight - d.weight).toNat : ℂ) + ((-(e.weight - d.weight)).toNat : ℂ)) =
        ((e.weight - d.weight).natAbs : ℂ) := by
      exact_mod_cast Int.toNat_add_toNat_neg_eq_natAbs (e.weight - d.weight)
    change nzExponent n ds (j : ℕ) - _ = _
    simp only [hjval]
    change (nzFullExponent n ds (pre.length + 1) - nzFullExponent n ds pre.length) -
      (((posWeight ds (pre.length + 1) - posWeight ds pre.length).toNat : ℂ) +
        ((-(posWeight ds (pre.length + 1) - posWeight ds pre.length)).toNat : ℂ)) / 2 = _
    rw [nzFullExponent, nzFullExponent, posWeight_append_cons_succ, posWeight_append_cons,
      posExponent_append_cons_succ, posExponent_append_cons, hweight]
    push_cast
    ring
  have hσre : σ.re < -1 := by
    rw [hσ, Complex.sub_re, Complex.sub_re, Complex.neg_re, Complex.one_re,
      Complex.ofReal_re]
    linarith [Nat.cast_nonneg (α := ℝ) (e.weight - d.weight).natAbs]
  have hφ (z : ℂ) : f (chart i j hj z) =
      Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) := by
    change nzFunction n ds
      (Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.swap ℂ i j) = _
    rw [swap_mul_transvection_mul_swap, nzFunction_transvection hj]
  intro hzero
  have h := LinearMap.congr_fun hzero ⟨f, hf⟩
  change (∫ z, f (chart i j hj z)) = 0 at h
  rw [show (fun z => f (chart i j hj z)) = _ from funext hφ,
    integral_one_add_norm_sq_cpow hσre] at h
  exact (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (ne_zero_of_re_pos (by simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith))) h

include hn hi hre in
/-- A strict adjacent swap has a nonzero intertwiner whose value at each
unitary matrix is the absolutely convergent rank-one chart integral. -/
theorem exists_strictSwapIntertwining :
    ∃ T : KFs n ds →ₗ[ℂ] KFs n es, T ≠ 0 ∧
      IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es) ds T ∧
      ∀ (k : unitaryCompact ℂ n) (f : KFs n ds),
        (T f : Langlands.GeneralLinear n ℂ → ℂ) (k : Langlands.GeneralLinear n ℂ) =
          ∫ z, f.val (chart i j hj z * (k : Langlands.GeneralLinear n ℂ)) := by
  let ℓ := strictSwapIntegral pre post d e i j hi hj hre
  have hℓ := strictSwapIntegral_ne_zero pre post d e i j hi hj hre
  have hJ := strictSwapIntegral_isJacquet pre post d e hn i j hi hj hre
  have hes : (es).length = n := (ComplexPermutation.length_swap pre post d e).trans hn
  obtain ⟨T, hT₁, hT⟩ := ComplexBlock.exists_embedding_eval_one ds es hes ℓ hℓ hJ
  refine ⟨T, ?_, ComplexPermutation.intertwining_of_embedding hT, ?_⟩
  · intro hzero
    apply hℓ
    apply LinearMap.ext
    intro f
    simpa only [hzero, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply] using (hT₁ f).symm
  · intro k f
    let k' := ComplexPermutation.toUnitary k
    have hK := congrFun (hT.1 k f) 1
    change (T (complexStandardRep n ds k' f) : Langlands.GeneralLinear n ℂ → ℂ) 1 =
      (T f : Langlands.GeneralLinear n ℂ → ℂ) (1 * (k : Langlands.GeneralLinear n ℂ)) at hK
    rw [one_mul, hT₁] at hK
    rw [← hK]
    change (∫ z, ((complexStandardRep n ds k' f : KFs n ds) :
      Langlands.GeneralLinear n ℂ → ℂ) (chart i j hj z)) = _
    rw [principalSeriesRep_apply_coe, ComplexPermutation.toUnits_toUnitary k]
    rfl

end AdjacentSwap

end Langlands.Archimedean.ComplexSwapJacquet
