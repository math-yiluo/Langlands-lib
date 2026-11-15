import Langlands.Representation.Archimedean.ComplexSwapJacquetLie
import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A test vector on which the rank-one Jacquet integral does not vanish

Let `ds = pre ++ d :: e :: post` have length `n`, let `i = |pre|` and `j = i + 1` be the
positions of `d` and `e`, and assume `Re(t_d - t_e) ≥ 0`. We find `c ∈ ℂ` and a `U(n)`-finite
`F ∈ complexStandardModule n ds` with `∫_ℂ integrand ds hn i j hj c F z dz ≠ 0`
(`exists_integral_integrand_ne_zero`).

The test vector is `F(g) = N(g s)`, where `N` is the nonvanishing `U(n)`-finite function
`nzFunction n ds` of `ComplexStandardNontrivialProof` (a product of powers of bottom-right minors,
their conjugates and real powers of Gram determinants of bottom rows) and `s` is the
permutation matrix of `(i j)`. Then `F(C(z)) = N(s x(z) s) = N(1 + z E_{ji})`. All bottom-right
minors of `1 + z E_{ji}` are `1`, and its Gram determinants are `1` except the one of the rows
`≥ j`, which is `1 + |z|²`. Hence `φ(z) = F(C(z)) = (1 + |z|²)^σ` with
`σ = -1 - (t_d - t_e) - |l_e - l_d| / 2` (`nzFunction_transvection`).

By `rightDerivative_chart_diag_j`, the integrand is
`(κ_i(c) - κ_j(c)) φ(z) + Dφ(z)(c z)`, and `Dφ(z)(c z) = 2 |z|² Re c σ φ(z) / (1 + |z|²)`.

* If `l_d = l_e`, take `c = 1`: `κ_i(1) - κ_j(1) = 2 (t_d - t_e) + 2` and the integrand is
  `(2 (t_d - t_e) + 2) (1 + |z|²)^(σ - 1)`, with integral `2π`.
* If `l_d ≠ l_e`, take `c = i`: `κ_i(i) - κ_j(i) = i (l_d - l_e)`, the derivative term vanishes,
  and the integral is `i (l_d - l_e) π / (-(σ + 1)) ≠ 0`.

Both use the radial integral `∫_ℂ (1 + |z|²)^β dz = π / (-(β + 1))` for `Re β < -1`
(`integral_one_add_norm_sq_cpow`), proved by `integral_fun_norm_addHaar` (polar coordinates)
and the fundamental theorem of calculus on `(0, ∞)` for the primitive
`(1 + r²)^(β + 1) / (2 (β + 1))` of `r (1 + r²)^β`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator

open MeasureTheory Filter Topology Set

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

/-! ## The radial integral -/

theorem ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ≠ 0 := by
  rintro rfl
  simp at hw

/-- `∫_ℂ (1 + |z|²)^β dz = π / (-(β + 1))` for `Re β < -1`, with the power written as
`exp(β log(1 + |z|²))`. -/
theorem integral_one_add_norm_sq_cpow {β : ℂ} (hβ : β.re < -1) :
    ∫ z : ℂ, Complex.exp (β * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) = (Real.pi : ℂ) / (-(β + 1)) := by
  have hβ1 : β + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  have hpos : ∀ r : ℝ, 0 < 1 + r ^ 2 := fun r => by positivity
  let g : ℝ → ℂ := fun r => Complex.exp (β * (Real.log (1 + r ^ 2) : ℂ))
  have hcont : Continuous fun z : ℂ => g ‖z‖ := by
    have hL : Continuous fun z : ℂ => Real.log (1 + ‖z‖ ^ 2) :=
      (continuous_const.add (continuous_norm.pow 2)).log fun z => (hpos ‖z‖).ne'
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hL))
  have hgint : Integrable (fun z : ℂ => g ‖z‖) := by
    have hr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < -2 * β.re := by
      rw [Complex.finrank_real_complex]
      push_cast
      linarith
    refine (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℂ)) hr).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun z => le_of_eq ?_)
    show ‖Complex.exp (β * (Real.log (1 + ‖z‖ ^ 2) : ℂ))‖ = _
    rw [Complex.norm_exp, Complex.re_mul_ofReal, Real.rpow_def_of_pos (hpos ‖z‖)]
    congr 1
    ring
  have hfun : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • g y) = fun y : ℝ => (y : ℂ) * g y := by
    funext y
    rw [Complex.finrank_real_complex]
    simp [Complex.real_smul]
  have hint : IntegrableOn (fun y : ℝ => (y : ℂ) * g y) (Ioi 0) := by
    have h := (integrable_fun_norm_addHaar (volume : Measure ℂ) (f := g)).mp hgint
    rwa [hfun] at h
  let F : ℝ → ℂ := fun r =>
    Complex.exp ((β + 1) * (Real.log (1 + r ^ 2) : ℂ)) / (2 * (β + 1))
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt F ((r : ℂ) * g r) r := by
    intro r _
    have hL : HasDerivAt (fun x : ℝ => Real.log (1 + x ^ 2)) (2 * r / (1 + r ^ 2)) r := by
      have h := ((hasDerivAt_pow 2 r).const_add 1).log (hpos r).ne'
      convert h using 1
      norm_num
    have h := ((hL.ofReal_comp.const_mul (β + 1)).cexp).div_const (2 * (β + 1))
    refine h.congr_deriv ?_
    have hexp : Complex.exp ((β + 1) * (Real.log (1 + r ^ 2) : ℂ)) =
        Complex.exp (β * (Real.log (1 + r ^ 2) : ℂ)) * ((1 + r ^ 2 : ℝ) : ℂ) := by
      rw [show (β + 1) * (Real.log (1 + r ^ 2) : ℂ) =
          β * (Real.log (1 + r ^ 2) : ℂ) + (Real.log (1 + r ^ 2) : ℂ) by ring,
        Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (hpos r)]
    show _ = (r : ℂ) * Complex.exp (β * (Real.log (1 + r ^ 2) : ℂ))
    rw [hexp]
    have h1 : (1 + (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (hpos r).ne'
    push_cast
    field_simp
  have htend : Tendsto F atTop (𝓝 0) := by
    have hL : Tendsto (fun r : ℝ => Real.log (1 + r ^ 2)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero))
    have hre : (β + 1).re < 0 := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have h1 : Tendsto (fun r : ℝ => Complex.exp ((β + 1) * (Real.log (1 + r ^ 2) : ℂ))) atTop
        (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (Real.tendsto_exp_atBot.comp (hL.const_mul_atTop_of_neg hre)).congr fun r => ?_
      simp only [Function.comp_apply, Complex.norm_exp, Complex.re_mul_ofReal]
    have h3 := h1.div_const (2 * (β + 1))
    rwa [zero_div] at h3
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  have hrad := integral_fun_norm_addHaar (volume : Measure ℂ) g
  have hvol : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real]
  have hF0 : F 0 = 1 / (2 * (β + 1)) := by simp [F]
  show ∫ z : ℂ, g ‖z‖ = _
  rw [hrad, hvol, hfun, hFTC, hF0, Complex.finrank_real_complex, nsmul_eq_mul, Complex.real_smul]
  field_simp
  push_cast
  ring

/-! ## The derivative of a radial power -/

/-- The derivative of `φ(z) = (1 + |z|²)^σ` in the direction `c z` is
`2 |z|² Re c σ φ(z) / (1 + |z|²)`. -/
theorem fderiv_exp_log_one_add_norm_sq_apply (σ c z : ℂ) :
    fderiv ℝ (fun z : ℂ => Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ))) z (c * z) =
      ((2 * ‖z‖ ^ 2 * c.re / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * σ *
        Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) := by
  have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + ‖z‖ ^ 2)) (‖z‖ ^ 2) := by
    have h := ((hasDerivAt_id (‖z‖ ^ 2)).const_add 1).log hpos.ne'
    simpa using h
  have hh := (h1.ofReal_comp.const_mul σ).cexp
  have hcomp := hh.hasFDerivAt.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hin : (2 • innerSL ℝ z) (c * z) = 2 * (‖z‖ ^ 2 * c.re) := by
    rw [_root_.smul_apply, innerSL_apply_apply, Complex.inner, nsmul_eq_mul,
      mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [show (fun z : ℂ => Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ))) =
      (fun x : ℝ => Complex.exp (σ * (Real.log (1 + x) : ℂ))) ∘ (fun z : ℂ => ‖z‖ ^ 2) from rfl,
    hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, hin,
    Complex.real_smul]
  push_cast
  field_simp

/-! ## Minors and Gram determinants of `1 + z E_ji` -/

section Minors

variable {n : ℕ}

/-- If the rows `≥ k` of `Y` vanish in the columns `< k`, the Gram determinant of these rows is
the squared absolute value of the bottom-right minor. -/
theorem lowGram_eq_normSq_lowMinor {Y : Matrix (Fin n) (Fin n) ℂ} {k : ℕ}
    (hY : ∀ a c : Fin n, k ≤ (a : ℕ) → (c : ℕ) < k → Y a c = 0) :
    lowGram k Y = (Complex.normSq (lowMinor k Y) : ℂ) := by
  have hR : Y.submatrix (Subtype.val : LowIdx n k → Fin n) id =
      Y.submatrix Subtype.val Subtype.val *
        (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Subtype.val : LowIdx n k → Fin n) id := by
    ext a c
    rw [Matrix.mul_apply]
    show Y a.1 c = ∑ b : LowIdx n k, Y a.1 b.1 * (1 : Matrix (Fin n) (Fin n) ℂ) b.1 c
    by_cases hc : k ≤ (c : ℕ)
    · rw [Finset.sum_eq_single ⟨c, hc⟩]
      · simp
      · intro b _ hb
        rw [Matrix.one_apply_ne (show (b : Fin n) ≠ c from fun h => hb (Subtype.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hY a.1 c a.2 (by omega)]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.one_apply_ne (fun h => hc (by rw [← h]; exact b.2)), mul_zero]
  rw [lowGram, hR, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix _ id),
    lowSelector_mul_conjTranspose, Matrix.one_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  exact Complex.mul_conj _

variable {i j : Fin n} (hj : (j : ℕ) = i + 1)
include hj

theorem transvection_isUpperTriangular (z : ℂ) :
    (Matrix.transvection i j z).IsUpperTriangular := by
  intro a b hab
  have hlt := lt_of_val_eq_succ hj
  have hab' : a ≠ b := ne_of_gt hab
  have hs : ¬(i = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hab (not_lt.mpr hlt.le)
  simp [Matrix.transvection, Matrix.one_apply_ne hab', hs]

theorem transvection_apply_self (z : ℂ) (a : Fin n) : Matrix.transvection i j z a a = 1 := by
  have hij := ne_of_val_eq_succ hj
  have hs : ¬(i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
  simp [Matrix.transvection, hs]

omit hj in
theorem transvection_eq_transpose (z : ℂ) :
    Matrix.transvection j i z = (Matrix.transvection i j z)ᵀ := by
  rw [Matrix.transvection, Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

/-- All bottom-right minors of `1 + z E_ji` are `1`. -/
theorem lowMinor_transvection (k : ℕ) (z : ℂ) : lowMinor k (Matrix.transvection j i z) = 1 := by
  rw [lowMinor, transvection_eq_transpose, ← Matrix.transpose_submatrix, Matrix.det_transpose,
    det_lowBlock_of_isUpperTriangular k (transvection_isUpperTriangular hj z)]
  exact Finset.prod_eq_one fun a _ => transvection_apply_self hj z a.1

/-- The Gram determinants of the rows `≥ k` of `1 + z E_ji` are `1` for `k ≠ j`. -/
theorem lowGram_transvection_of_ne {k : ℕ} (hk : k ≠ j) (z : ℂ) :
    lowGram k (Matrix.transvection j i z) = 1 := by
  rw [lowGram_eq_normSq_lowMinor (fun a c ha hc => ?_), lowMinor_transvection hj]
  · simp
  · have hac : a ≠ c := fun h => by
      rw [h] at ha
      omega
    have hs : ¬(j = a ∧ i = c) := by
      rintro ⟨rfl, rfl⟩
      omega
    simp [Matrix.transvection, Matrix.one_apply_ne hac, hs]

/-- The Gram determinant of the rows `≥ j` of `1 + z E_ji` is `1 + |z|²`. -/
theorem lowGram_transvection_self (z : ℂ) :
    lowGram (j : ℕ) (Matrix.transvection j i z) = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
  have hij := ne_of_val_eq_succ hj
  have hR : (Matrix.transvection j i z).submatrix (Subtype.val : LowIdx n j → Fin n) id *
      ((Matrix.transvection j i z).submatrix (Subtype.val : LowIdx n j → Fin n) id)ᴴ =
        (Matrix.transvection j i z * (Matrix.transvection j i z)ᴴ).submatrix
          Subtype.val Subtype.val := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
  have hYY : Matrix.transvection j i z * (Matrix.transvection j i z)ᴴ =
      1 + Matrix.single j i z + Matrix.single i j (star z) + Matrix.single j j (z * star z) := by
    rw [Matrix.transvection, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_single, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one, Matrix.single_mul_single_same]
    abel
  have hD : (Matrix.transvection j i z * (Matrix.transvection j i z)ᴴ).submatrix
      (Subtype.val : LowIdx n j → Fin n) Subtype.val =
        Matrix.diagonal (fun a : LowIdx n j => if (a : Fin n) = j then 1 + z * star z else 1) := by
    rw [hYY]
    ext a b
    have hai : i ≠ a.1 := fun h => by
      have := a.2
      rw [← h] at this
      omega
    have hbi : i ≠ b.1 := fun h => by
      have := b.2
      rw [← h] at this
      omega
    by_cases hab : a = b
    · subst hab
      by_cases ha : (a : Fin n) = j
      · simp [ha, hij]
      · simp [ha, Ne.symm ha, hai]
    · have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      have hjj : ¬(j = a.1 ∧ j = b.1) := fun h => hab' (h.1.symm.trans h.2)
      simp [Matrix.one_apply_ne hab', hab, hai, hbi, hjj]
  rw [lowGram, hR, hD, Matrix.det_diagonal, Finset.prod_eq_single ⟨j, le_rfl⟩]
  · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro b _ hb
    have hb' : (b : Fin n) ≠ j := fun h => hb (Subtype.ext h)
    simp [hb']
  · simp

omit hj in
/-- `s x(z) s = 1 + z E_ji`. -/
theorem swap_mul_transvection_mul_swap (z : ℂ) :
    Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.swap ℂ i j =
      Matrix.transvection j i z := by
  rw [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.swap_mul_self,
    swap_mul_single, Equiv.swap_apply_left, single_mul_swap, Equiv.swap_apply_right,
    Matrix.transvection]

/-- `N(1 + z E_ji) = (1 + |z|²)^σ_j` for the nonvanishing function `N = nzFunction n ds`. -/
theorem nzFunction_transvection (ds : List ComplexCharacterData) (z : ℂ) :
    nzFunction n ds (Matrix.transvection j i z) =
      Complex.exp ((nzExponent n ds j -
        (((nzWeight ds j).toNat : ℂ) + ((-nzWeight ds j).toNat : ℂ)) / 2) *
          (Real.log (1 + ‖z‖ ^ 2) : ℂ)) := by
  rw [nzFunction, Finset.prod_eq_single j]
  · rw [nzFactor, minorFactor, lowMinor_transvection hj, lowGram_transvection_self hj,
      Complex.ofReal_re]
    simp
  · intro k _ hk
    rw [nzFactor, minorFactor, lowMinor_transvection hj,
      lowGram_transvection_of_ne hj (fun h => hk (Fin.ext h))]
    simp
  · simp

end Minors

/-! ## The test vector -/

section TestVector

variable {n : ℕ}

/-- The nonvanishing function `g ↦ N(g)` of `ComplexStandardNontrivialProof` is a `U(n)`-finite
vector of the standard module. -/
theorem nzFunction_mem_kFiniteFunctions (ds : List ComplexCharacterData) :
    (fun g : Langlands.GeneralLinear n ℂ => nzFunction n ds (g : Matrix (Fin n) (Fin n) ℂ)) ∈
      kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) := by
  let f : Langlands.GeneralLinear n ℂ → ℂ :=
    fun g => nzFunction n ds (g : Matrix (Fin n) (Fin n) ℂ)
  have hsmooth : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f :=
    contMDiff_of_contDiffOn (contDiffOn_nzFunction ds) fun g => rfl
  have heq : ∀ (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ),
      f ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
          (u : Langlands.GeneralLinear n ℂ) * g) =
        principalSeriesCharacter ℂ n (complexPositionCharacter ds) a * f g := by
    intro a u g
    have hu : ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular ∧
        ∀ i, ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := u.2
    have hb : (Matrix.diagonal (fun i => (a i : ℂ)) *
        ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)).IsUpperTriangular :=
      (Matrix.blockTriangular_diagonal _).mul hu.1
    have hbd : ∀ i, (Matrix.diagonal (fun i => (a i : ℂ)) *
        ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) i i = a i := by
      intro i
      rw [Matrix.diagonal_mul, hu.2 i, mul_one]
    show nzFunction n ds (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) = _
    rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val,
      nzFunction_mul_of_isUpperTriangular ds hb (fun i => by rw [hbd]; exact (a i).ne_zero)
        (Units.isUnit g), principalSeriesCharacter_eq]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hbd]
    rfl
  exact ⟨⟨hsmooth, heq⟩, nzFunction_mem ds⟩

theorem swap_mem_unitaryCompact (i j : Fin n) :
    (Matrix.GeneralLinearGroup.swap ℂ i j : Langlands.GeneralLinear n ℂ) ∈
      unitaryCompact ℂ n := by
  rw [mem_unitaryCompact_iff]
  show star (Matrix.swap ℂ i j) * Matrix.swap ℂ i j = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_swap, Matrix.swap_mul_self]

end TestVector

/-! ## Positions in `pre ++ d :: e :: post` -/

theorem posWeight_append_cons (pre : List ComplexCharacterData) (d : ComplexCharacterData)
    (l : List ComplexCharacterData) : posWeight (pre ++ d :: l) pre.length = d.weight := by
  induction pre with
  | nil => rfl
  | cons a pre ih => exact ih

theorem posExponent_append_cons (pre : List ComplexCharacterData) (d : ComplexCharacterData)
    (l : List ComplexCharacterData) : posExponent (pre ++ d :: l) pre.length = d.exponent := by
  induction pre with
  | nil => rfl
  | cons a pre ih => exact ih

theorem posWeight_append_cons_succ (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) :
    posWeight (pre ++ d :: e :: post) (pre.length + 1) = e.weight := by
  induction pre with
  | nil => rfl
  | cons a pre ih => exact ih

theorem posExponent_append_cons_succ (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) :
    posExponent (pre ++ d :: e :: post) (pre.length + 1) = e.exponent := by
  induction pre with
  | nil => rfl
  | cons a pre ih => exact ih

/-! ## The nonvanishing integral -/

/-- For `Re(t_d - t_e) ≥ 0` there are `c` and a `U(n)`-finite vector `F` of the standard module
of `pre ++ d :: e :: post` on which the rank-one Jacquet integral `∫ integrand c F` is
nonzero. -/
theorem exists_integral_integrand_ne_zero (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (n : ℕ) (hn : (pre ++ d :: e :: post).length = n)
    (i j : Fin n) (hi : (i : ℕ) = pre.length) (hj : (j : ℕ) = i + 1)
    (hre : 0 ≤ (d.exponent - e.exponent).re) (_hne : d.weight ≠ e.weight ∨ d.exponent ≠ e.exponent) :
    ∃ (c : ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ),
      f ∈ kFiniteFunctions (complexStandardModule n (pre ++ d :: e :: post)) (unitaryCompact ℂ n) ∧
        ∫ z, integrand (pre ++ d :: e :: post) hn i j hj c f z ≠ 0 := by
  have hjval : (j : ℕ) = pre.length + 1 := by omega
  have hre' : 0 ≤ d.exponent.re - e.exponent.re := by simpa using hre
  let s0 : Langlands.GeneralLinear n ℂ := Matrix.GeneralLinearGroup.swap ℂ i j
  let F0 : Langlands.GeneralLinear n ℂ → ℂ :=
    fun g => nzFunction n (pre ++ d :: e :: post) (g : Matrix (Fin n) (Fin n) ℂ)
  let F := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) s0 F0
  have hF : F ∈ kFiniteFunctions (complexStandardModule n (pre ++ d :: e :: post))
      (unitaryCompact ℂ n) :=
    rightTranslation_mem_kFiniteFunctions_complexStandardModule n _
      (nzFunction_mem_kFiniteFunctions _) (swap_mem_unitaryCompact i j)
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℂ, σ = nzExponent n (pre ++ d :: e :: post) j -
      (((nzWeight (pre ++ d :: e :: post) j).toNat : ℂ) +
        ((-nzWeight (pre ++ d :: e :: post) j).toNat : ℂ)) / 2 := ⟨_, rfl⟩
  have hσ : σ = -1 - (d.exponent - e.exponent) -
      ((((e.weight - d.weight).natAbs : ℝ) / 2 : ℝ) : ℂ) := by
    rw [hσdef, hjval]
    have h1 : nzExponent n (pre ++ d :: e :: post) (pre.length + 1) =
        nzFullExponent n (pre ++ d :: e :: post) (pre.length + 1) -
          nzFullExponent n (pre ++ d :: e :: post) pre.length := rfl
    have h2 : nzWeight (pre ++ d :: e :: post) (pre.length + 1) =
        posWeight (pre ++ d :: e :: post) (pre.length + 1) -
          posWeight (pre ++ d :: e :: post) pre.length := rfl
    have h3 : (((e.weight - d.weight).toNat : ℂ) + ((-(e.weight - d.weight)).toNat : ℂ)) =
        ((e.weight - d.weight).natAbs : ℂ) := by
      exact_mod_cast Int.toNat_add_toNat_neg_eq_natAbs (e.weight - d.weight)
    rw [h1, h2, nzFullExponent, nzFullExponent, posWeight_append_cons_succ, posWeight_append_cons,
      posExponent_append_cons_succ, posExponent_append_cons, h3]
    push_cast
    ring
  have hφ : (fun z => F (chart i j hj z)) =
      fun z => Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) := by
    funext z
    show nzFunction n (pre ++ d :: e :: post)
      (Matrix.swap ℂ i j * Matrix.transvection i j z * Matrix.swap ℂ i j) = _
    rw [swap_mul_transvection_mul_swap, nzFunction_transvection hj, hσdef]
  have hint_eq : ∀ c z : ℂ, integrand (pre ++ d :: e :: post) hn i j hj c F z =
      (kappa (pre ++ d :: e :: post) hn i c - kappa (pre ++ d :: e :: post) hn j c) *
          Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) +
        ((2 * ‖z‖ ^ 2 * c.re / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * σ *
          Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) := by
    intro c z
    have hFz : F (chart i j hj z) = Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) :=
      congrFun hφ z
    rw [integrand, rightDerivative_chart_diag_j hn hj (Submodule.mem_inf.mp hF).1 c z, hφ,
      fderiv_exp_log_one_add_norm_sq_apply, hFz]
    ring
  rcases eq_or_ne d.weight e.weight with hm | hm
  · -- equal weights: `c = 1`
    refine ⟨1, F, hF, ?_⟩
    have hσ0 : σ = -1 - (d.exponent - e.exponent) := by
      rw [hσ, hm, sub_self]
      simp
    have hκ : kappa (pre ++ d :: e :: post) hn i 1 - kappa (pre ++ d :: e :: post) hn j 1 =
        2 * (d.exponent - e.exponent) + 2 := by
      rw [kappa_eq, kappa_eq, hi, hjval, posExponent_append_cons, posExponent_append_cons_succ]
      simp only [Complex.one_re, Complex.one_im]
      push_cast
      ring
    have hpt : ∀ z : ℂ, integrand (pre ++ d :: e :: post) hn i j hj 1 F z =
        (2 * (d.exponent - e.exponent) + 2) *
          Complex.exp ((σ - 1) * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) := by
      intro z
      have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
      have hE : Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) =
          Complex.exp ((σ - 1) * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
        rw [show σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ) =
            (σ - 1) * (Real.log (1 + ‖z‖ ^ 2) : ℂ) + (Real.log (1 + ‖z‖ ^ 2) : ℂ) by ring,
          Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
      have h1 : (1 + (‖z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [hint_eq, hκ, hE, hσ0, Complex.one_re]
      push_cast
      field_simp
      ring
    rw [show (fun z => integrand (pre ++ d :: e :: post) hn i j hj 1 F z) = _ from funext hpt,
      integral_const_mul, integral_one_add_norm_sq_cpow]
    · refine mul_ne_zero (ne_zero_of_re_pos ?_) (div_ne_zero ?_ (ne_zero_of_re_pos ?_))
      · simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
          Complex.sub_re, Complex.sub_im]
        norm_num
        linarith
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · rw [hσ0]
        simp only [Complex.neg_re, Complex.add_re, Complex.sub_re, Complex.one_re]
        linarith
    · rw [hσ0]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
  · -- different weights: `c = i`
    refine ⟨Complex.I, F, hF, ?_⟩
    have hκ : kappa (pre ++ d :: e :: post) hn i Complex.I -
        kappa (pre ++ d :: e :: post) hn j Complex.I =
          Complex.I * ((d.weight : ℂ) - (e.weight : ℂ)) := by
      rw [kappa_eq, kappa_eq, hi, hjval, posWeight_append_cons, posWeight_append_cons_succ]
      simp only [Complex.I_re, Complex.I_im]
      push_cast
      ring
    have hpt : ∀ z : ℂ, integrand (pre ++ d :: e :: post) hn i j hj Complex.I F z =
        (Complex.I * ((d.weight : ℂ) - (e.weight : ℂ))) *
          Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ)) := by
      intro z
      rw [hint_eq, hκ, Complex.I_re]
      simp
    have hnat : (1 : ℝ) ≤ ((e.weight - d.weight).natAbs : ℝ) := by
      have h0 : (e.weight - d.weight).natAbs ≠ 0 :=
        Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hm))
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hσre : σ.re < -1 := by
      rw [hσ]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.ofReal_re]
      linarith
    rw [show (fun z => integrand (pre ++ d :: e :: post) hn i j hj Complex.I F z) = _ from
      funext hpt, integral_const_mul, integral_one_add_norm_sq_cpow hσre]
    refine mul_ne_zero (mul_ne_zero Complex.I_ne_zero ?_) (div_ne_zero ?_ (ne_zero_of_re_pos ?_))
    · rw [sub_ne_zero]
      exact_mod_cast hm
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      linarith

end Langlands.Archimedean.ComplexSwapJacquet
