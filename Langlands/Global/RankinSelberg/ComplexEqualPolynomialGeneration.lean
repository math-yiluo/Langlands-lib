import Langlands.Global.RankinSelberg.ComplexEqualSpectralMultiplication
import Langlands.Global.RankinSelberg.OrdinaryPolynomialGeneration
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness
import Langlands.Global.RankinSelberg.ArchimedeanComplexPairFactor

/-! # Polynomial Gaussian row tests under radial differentiation -/

noncomputable section

open MvPolynomial
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexEqualPolynomialGeneration

open ComplexEqualSpectralMultiplication (radialDerivative radialDerivative_apply)

variable {r : ℕ}
local notation "Row" => Fin (r + 1) → ℂ
local notation "Coordinates" => Fin (r + 1) × Bool
local notation "Poly" => MvPolynomial Coordinates ℂ

private def rowCoordinates (v : Row) (i : Coordinates) : ℂ :=
  if i.2 then ((v i.1).im : ℂ) else ((v i.1).re : ℂ)

private def rowSqNorm (v : Row) : ℝ := ∑ j, ‖v j‖ ^ 2

/-- The given row Schwartz map is a polynomial in the real and imaginary coordinates
times the Gaussian of scale `c`. The standard complex test has scale `2 * π`. -/
def IsGaussianPolynomialRow (c : ℝ) (Φ : 𝓢(Row, ℂ)) : Prop :=
  ∃ p : Poly, ∀ v : Row, Φ v = eval (rowCoordinates v) p * (Real.exp (-c * rowSqNorm v) : ℂ)

private theorem rowCoordinates_smul (x : ℝ) (v : Row) (i : Coordinates) :
    rowCoordinates (x • v) i = (x : ℂ) * rowCoordinates v i := by
  obtain ⟨j, b⟩ := i
  cases b <;> simp [rowCoordinates, Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im]

private theorem rowSqNorm_smul (x : ℝ) (v : Row) : rowSqNorm (x • v) = x ^ 2 * rowSqNorm v := by
  simp only [rowSqNorm, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]

private theorem hasDerivAt_rowCoordinate (v : Row) (i : Coordinates) :
    HasDerivAt (fun x : ℝ => rowCoordinates (Real.exp x • v) i) (rowCoordinates v i) 0 := by
  simp_rw [rowCoordinates_smul]
  simpa only [Real.exp_zero, Complex.ofReal_one, one_mul] using
    ((Real.hasDerivAt_exp (0 : ℝ)).ofReal_comp).mul_const (rowCoordinates v i)

private theorem exists_deriv_evaluation (p : Poly) :
    ∃ q : Poly, ∀ v : Row,
      HasDerivAt (fun x : ℝ => eval (rowCoordinates (Real.exp x • v)) p) (eval (rowCoordinates v) q) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun v => ?_⟩
    simpa only [eval_C, map_zero] using (hasDerivAt_const (0 : ℝ) a)
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', fun v => ?_⟩
    simpa only [map_add, Pi.add_def] using (hp' v).add (hq' v)
  | mul_X p i hp =>
    obtain ⟨q, hq⟩ := hp
    refine ⟨(q + p) * X i, fun v => ?_⟩
    simpa only [map_mul, map_add, eval_X, Pi.mul_def, Real.exp_zero, one_smul, add_mul, add_comm] using
      (hq v).mul (hasDerivAt_rowCoordinate v i)

private def rowSqNormPolynomial : Poly :=
  ∑ j : Fin (r + 1), (X (j, false) ^ 2 + X (j, true) ^ 2)

private theorem eval_rowSqNormPolynomial (v : Row) :
    eval (rowCoordinates v) rowSqNormPolynomial = (rowSqNorm v : ℂ) := by
  simp only [rowSqNorm, rowSqNormPolynomial, Complex.ofReal_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, map_pow, eval_X, rowCoordinates, Bool.false_eq_true, ite_false, ite_true,
    ← Complex.ofReal_pow, ← Complex.ofReal_add]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private theorem hasDerivAt_rowGaussian (c : ℝ) (v : Row) :
    HasDerivAt (fun x : ℝ => (Real.exp (-c * rowSqNorm (Real.exp x • v)) : ℂ))
      ((-2 * (c : ℂ) * (rowSqNorm v : ℂ)) * (Real.exp (-c * rowSqNorm v) : ℂ)) 0 := by
  have hE := (((Real.hasDerivAt_exp (0 : ℝ)).pow 2).const_mul (-c)).mul_const (rowSqNorm v)
  have hG := hE.exp.ofReal_comp
  simp only [rowSqNorm_smul, Pi.pow_apply, ← mul_assoc, Real.exp_zero, one_pow, mul_one,
    Complex.ofReal_mul, Complex.ofReal_neg] at hG ⊢
  convert hG using 1
  norm_num
  ring

/-- Radial differentiation preserves polynomial Gaussian row tests of the same scale. -/
theorem isGaussianPolynomialRow_radialDerivative {c : ℝ} {Φ : 𝓢(Row, ℂ)}
    (hΦ : IsGaussianPolynomialRow c Φ) : IsGaussianPolynomialRow c (radialDerivative Φ) := by
  obtain ⟨p, hp⟩ := hΦ
  obtain ⟨q, hq⟩ := exists_deriv_evaluation p
  refine ⟨q - C (2 * (c : ℂ)) * rowSqNormPolynomial * p, fun v => ?_⟩
  have hF : HasDerivAt (fun x : ℝ => Φ (Real.exp x • v)) (radialDerivative Φ v) 0 := by
    simpa only [Real.exp_zero, one_smul, Function.comp_def, radialDerivative_apply] using
      (Φ.hasFDerivAt (Real.exp 0 • v)).comp_hasDerivAt (0 : ℝ)
        ((Real.hasDerivAt_exp (0 : ℝ)).smul_const v)
  have hProduct := (hq v).mul (hasDerivAt_rowGaussian c v)
  have hEq : (fun x : ℝ => Φ (Real.exp x • v)) = fun x : ℝ =>
      eval (rowCoordinates (Real.exp x • v)) p * (Real.exp (-c * rowSqNorm (Real.exp x • v)) : ℂ) :=
    funext fun x => hp (Real.exp x • v)
  rw [hEq] at hF
  rw [hF.unique hProduct]
  simp only [Real.exp_zero, one_smul, map_sub, map_mul, eval_C, eval_rowSqNormPolynomial]
  ring

section EqualTests

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean ArchimedeanLocal MeasureTheory
open ComplexEqualSpectralMultiplication (complexEqualSpectralMultiplication)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- Ordinary equal tests with row Schwartz functions of the specified polynomial Gaussian form. -/
abbrev GaussianEqualTest (r : ℕ) (d e : List ComplexCharacterData) (a : ℂˣ) (c : ℝ) :=
  complexWhittakerModel r d a × complexWhittakerModel r e (-a) ×
    {Φ : 𝓢((Fin (r + 1) → ℂ), ℂ) // IsGaussianPolynomialRow c Φ}

/-- Restriction of the ordinary equal test integral to polynomial Gaussian row tests. -/
def gaussianEqualIntegral (r : ℕ) (d e : List ComplexCharacterData) (a : ℂˣ) (c : ℝ)
    (D : ComplexQuotientMeasureData r) (i : GaussianEqualTest r d e a c) : ℂ → ℂ :=
  complexOrdinaryEqualTest r d e a D (i.1, i.2.1, i.2.2.val)

private theorem polynomialGaussianEqual_smul (r : ℕ) (d e : List ComplexCharacterData)
    (a : ℂˣ) (c : ℝ) (D : ComplexQuotientMeasureData r) (k : ℂ) {p : Polynomial ℂ}
    (hp : IsOrdinaryNormalizationPolynomial (gaussianEqualIntegral r d e a c D) (complexPairLFactor d e) p) :
    IsOrdinaryNormalizationPolynomial (gaussianEqualIntegral r d e a c D) (complexPairLFactor d e) (k • p) := by
  obtain ⟨⟨W, V, Φ⟩, N, hN⟩ := hp
  let i : GaussianEqualTest r d e a c := (k • W, V, Φ)
  have hi (s : ℂ) : gaussianEqualIntegral r d e a c D i s =
      k * gaussianEqualIntegral r d e a c D (W, V, Φ) s := by
    simp only [i, gaussianEqualIntegral, complexOrdinaryEqualTest, complexEqualIntegral, ArchimedeanLocal.equalIntegral,
      ArchimedeanLocal.equalIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  refine ⟨i, ⟨fun s => k * N.value s, fun s hs => analyticAt_const.mul (N.analytic s hs), ?_⟩, fun s => ?_⟩
  · obtain ⟨b, hb⟩ := N.eq_on_right
    exact ⟨b, fun s hs => by rw [hi s, hb s hs, mul_assoc]⟩
  · change k * N.value s = (k • p).eval s
    rw [hN, Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]

/-- If ordinary equal-rank tests with polynomial Gaussian rows have polynomial
normalizations covering every point, they give an ordinary finite sum equal to one. -/
def ComplexEqualFiniteSumFromPolynomialsStatement : Prop :=
  ∀ (r : ℕ) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = r + 1 →
    ∀ (a : ℂˣ) (c : ℝ) (D : ComplexQuotientMeasureData r),
    let I := gaussianEqualIntegral r d e a c D
    let L := complexPairLFactor d e
    (∀ i, ∃ (p : Polynomial ℂ) (N : OrdinaryIntegralNormalization (I i) (fun s => (L.denominator s)⁻¹)),
      ∀ s, N.value s = p.eval s) →
    HasCoveringOrdinaryNormalizations I L →
    HasFiniteOrdinaryNormalizationSum (complexOrdinaryEqualTest r d e a D) L

set_option maxHeartbeats 1200000 in
theorem complexEqualFiniteSumFromPolynomials : ComplexEqualFiniteSumFromPolynomialsStatement := by
  intro r d e hd he a c D I L hPoly hCover
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0 :=
    ArchimedeanComplexPairFactor.complexLFactor_ne_zero _
  have hSum : HasFiniteOrdinaryNormalizationSum I L := by
    refine ordinaryPolynomialGeneration I L ?_ (fun k p hp => polynomialGaussianEqual_smul r d e a c D k hp) ?_
    · intro s
      obtain ⟨i, N, hN⟩ := hCover s
      obtain ⟨p, M, hM⟩ := hPoly i
      have hw := N.value_eq_of_factor_ne_zero M ⟨b, fun z hz => inv_ne_zero (hb z hz)⟩
      rw [hw, hM] at hN
      exact ⟨p, ⟨i, M, hM⟩, hN⟩
    · intro p hp
      obtain ⟨⟨W, V, Φ⟩, N, hN⟩ := hp
      let Ψ : {Φ : 𝓢((Fin (r + 1) → ℂ), ℂ) // IsGaussianPolynomialRow c Φ} :=
        ⟨radialDerivative Φ.val, isGaussianPolynomialRow_radialDerivative Φ.2⟩
      obtain ⟨p', N', hN'⟩ := hPoly (W, V, Ψ)
      obtain ⟨b₀, hb₀⟩ := complexEqualSpectralMultiplication r d e hd he a D W V Φ.val
      obtain ⟨bI, hI⟩ := N.eq_on_right
      obtain ⟨b', h'⟩ := N'.eq_on_right
      let B := max b (max b₀ (max bI b'))
      let n : ℂ := r + 1
      let κ := (d.map ComplexCharacterData.exponent).sum + (e.map ComplexCharacterData.exponent).sum
      let q : Polynomial ℂ := n⁻¹ • ((-(1 / 2 : ℂ)) • p' - κ • p)
      have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast Nat.succ_ne_zero r
      have hpq : Polynomial.X * p = q := by
        apply Polynomial.eq_of_infinite_eval_eq
        have hInf : (Complex.ofReal '' Set.Ioi B).Infinite :=
          (Set.Ioi_infinite B).image Complex.ofReal_injective.injOn
        apply hInf.mono
        rintro z ⟨x, hx, rfl⟩
        let s : ℂ := x
        have hs : B < s.re := by simpa only [s, Complex.ofReal_re, Set.mem_Ioi] using hx
        have hmax := (le_max_right b _).trans_lt hs
        have hmax' := (le_max_right b₀ _).trans_lt hmax
        have h₀ := hI s ((le_max_left bI _).trans_lt hmax')
        have h₁ := h' s ((le_max_right bI _).trans_lt hmax')
        have hD := hb₀ s ((le_max_left b₀ _).trans_lt hmax)
        change I (W, V, Ψ) s = (-2 * (n * s + (d.map ComplexCharacterData.exponent).sum +
          (e.map ComplexCharacterData.exponent).sum)) * I (W, V, Φ) s at hD
        rw [h₁, h₀, hN', hN, ← mul_assoc] at hD
        have hh := mul_right_cancel₀ (inv_ne_zero (hb s ((le_max_left b _).trans_lt hs))) hD
        change (Polynomial.X * p).eval s = q.eval s
        apply mul_left_cancel₀ hn
        simp only [q, Polynomial.eval_sub, Polynomial.smul_eq_C_mul, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X]
        rw [← mul_assoc n n⁻¹ _, mul_inv_cancel₀ hn, one_mul]
        dsimp only [κ]
        linear_combination (1 / 2 : ℂ) * hh
      rw [hpq]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, N', hN'⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, N, hN⟩)))
  obtain ⟨m, j, N, hN⟩ := hSum
  exact ⟨m, fun k => ((j k).1, (j k).2.1, (j k).2.2.val), N, hN⟩

end EqualTests

end Langlands.Global.RankinSelbergGlobal.ComplexEqualPolynomialGeneration
