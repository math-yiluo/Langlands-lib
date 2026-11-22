import Langlands.Global.RankinSelberg.ComplexEqualPolynomialGeneration
import Langlands.Global.RankinSelberg.ComplexRankZeroWhittaker
import Langlands.Global.RankinSelberg.ComplexTatePolynomialGaussian

/-! # Polynomial normalization and generation of complex rank-one Gaussian row tests -/

noncomputable section

open Complex MvPolynomial Set
open scoped ComplexConjugate SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexRankZero

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open ComplexEqualPolynomialGeneration (GaussianEqualTest IsGaussianPolynomialRow gaussianEqualIntegral)
open Langlands.LocalFactor.ComplexTate (polynomialGaussian polynomialGaussian_apply
  complexTatePolynomialGaussian normalizedZeta_eq_right zeta_gaussian gaussian gaussSchwartz gaussSchwartz_apply)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "Row" => Fin (0 + 1) → ℂ
local notation "Coordinates" => Fin (0 + 1) × Bool
local notation "scale" => (2 * Real.pi : ℝ)
local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

private def realLinearCoordinate (b : Bool) : MvPolynomial Bool ℂ :=
  if b then (X false - X true) * C ((2 * I)⁻¹) else (X false + X true) * C (2 : ℂ)⁻¹

private theorem eval_realLinearCoordinate (z : ℂ) (b : Bool) :
    eval (fun c : Bool => if c then conj z else z) (realLinearCoordinate b) =
      if b then (z.im : ℂ) else (z.re : ℂ) := by
  have h : z + conj z = 2 * (z.re : ℂ) := by
    apply Complex.ext <;> simp [two_mul]
  have h' : z - conj z = 2 * I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, two_mul, add_mul]
  have hn : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  cases b
  · simp only [realLinearCoordinate, Bool.false_eq_true, ite_false, map_mul, map_add, eval_X, ite_true, eval_C, h]
    ring
  · simp only [realLinearCoordinate, ite_true, map_mul, map_sub, eval_X, Bool.false_eq_true, ite_false, eval_C, h']
    rw [mul_right_comm, mul_inv_cancel₀ hn, one_mul]

private theorem exists_polynomialGaussian_eq_lineSchwartz {Φ : 𝓢(Row, ℂ)}
    (hΦ : IsGaussianPolynomialRow scale Φ) :
    ∃ p : MvPolynomial Bool ℂ, lineSchwartz Φ = polynomialGaussian p := by
  obtain ⟨Q, hQ⟩ := hΦ
  let p := C (Real.pi : ℂ) * bind₁ (fun i : Coordinates => realLinearCoordinate i.2) Q
  refine ⟨p, ?_⟩
  ext z
  have hz := hQ (fun _ => z)
  change Φ (fun _ => z) = eval (fun i : Coordinates => if i.2 then (z.im : ℂ) else (z.re : ℂ)) Q *
    (Real.exp (-scale * (∑ _ : Fin (0 + 1), ‖z‖ ^ 2)) : ℂ) at hz
  have hBind (w : ℂ) : eval (fun c : Bool => if c then conj w else w)
      (bind₁ (fun i : Coordinates => realLinearCoordinate i.2) Q) =
      eval (fun i : Coordinates => if i.2 then (w.im : ℂ) else (w.re : ℂ)) Q := by
    simpa only [aeval_eq_eval, eval_realLinearCoordinate] using
      aeval_bind₁ (fun c : Bool => if c then conj w else w)
        (fun i : Coordinates => realLinearCoordinate i.2) Q
  rw [lineSchwartz_apply, hz, Fin.sum_univ_one, polynomialGaussian_apply]
  dsimp only [p]
  rw [map_mul, eval_C, hBind, gaussian, ite_eq_left (le_refl (0 : ℤ))]
  simp only [Int.natAbs_zero, pow_zero, one_mul, ofReal_exp]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]

private def lineLift (Φ : 𝓢(ℂ, ℂ)) : 𝓢(Row, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.funUnique (Fin (0 + 1)) ℝ ℂ) Φ

private theorem lineSchwartz_lineLift (f : 𝓢(ℂ, ℂ)) : lineSchwartz (lineLift f) = f := by
  ext z
  rfl

private theorem zeta_shift (f : ℂ → ℂ) (m : ℤ) (t s : ℂ) :
    ComplexTate.zeta f m t s = Langlands.LocalFactor.ComplexTate.zeta f m (s + t) := rfl

private theorem isGaussianPolynomialRow_lineLift_gaussSchwartz (k : ℂ) (m : ℤ) :
    IsGaussianPolynomialRow scale (lineLift (k • gaussSchwartz m)) := by
  let x : MvPolynomial Coordinates ℂ := X (0, false)
  let y : MvPolynomial Coordinates ℂ := X (0, true) * C I
  refine ⟨C (k / (Real.pi : ℂ)) * (if 0 ≤ m then (x - y) ^ m.natAbs else (x + y) ^ m.natAbs), fun v => ?_⟩
  let p : Coordinates → ℂ := fun i => if i.2 then ((v i.1).im : ℂ) else ((v i.1).re : ℂ)
  change k * gaussSchwartz m (v 0) = eval p _ *
    (Real.exp (-scale * (∑ j : Fin (0 + 1), ‖v j‖ ^ 2)) : ℂ)
  have h₁ : eval p (x + y) = v 0 := by
    simpa only [x, y, p, map_add, map_mul, eval_X, eval_C, Bool.false_eq_true, ite_false, ite_true] using
      re_add_im (v 0)
  have h₂ : eval p (x - y) = conj (v 0) := by
    simp only [x, y, p, map_sub, map_mul, eval_X, eval_C, Bool.false_eq_true, ite_false, ite_true]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hE : (Real.exp (-scale * ‖v 0‖ ^ 2) : ℂ) =
      Complex.exp (-2 * (Real.pi : ℂ) * (‖v 0‖ : ℂ) ^ 2) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  rw [gaussSchwartz_apply, gaussian, Fin.sum_univ_one, hE, map_mul, eval_C]
  by_cases hm : 0 ≤ m
  · rw [ite_eq_left hm, ite_eq_left hm, map_pow, h₂]
    ring
  · rw [ite_eq_right hm, ite_eq_right hm, map_pow, h₁]
    ring

/-- In complex rank one, all standard Gaussian row tests normalize to polynomials.
If both models are nonzero, one such test has normalized value one. -/
def ComplexRankZeroGaussianGenerationStatement : Prop :=
  ∀ (d e : List ComplexCharacterData), d.length = 1 → e.length = 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData 0),
    let J := gaussianEqualIntegral 0 d e a scale D
    let L := complexPairLFactor d e
    (∀ i, ∃ (p : Polynomial ℂ) (N : OrdinaryIntegralNormalization (J i) (fun s => (L.denominator s)⁻¹)),
      ∀ s, N.value s = p.eval s) ∧
    (complexWhittakerModel 0 d a ≠ ⊥ → complexWhittakerModel 0 e (-a) ≠ ⊥ →
      ∃ (i : GaussianEqualTest 0 d e a scale)
        (N : OrdinaryIntegralNormalization (J i) (fun s => (L.denominator s)⁻¹)), ∀ s, N.value s = 1)

set_option maxHeartbeats 900000 in
theorem complexRankZeroGaussianGeneration : ComplexRankZeroGaussianGenerationStatement := by
  intro d e hd he a D
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hd
  obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp he
  obtain ⟨κ, hκ0, hκ⟩ := exists_measure_eq D
  let d := c.mul c'
  let L := complexPairLFactor [c] [c']
  let J := gaussianEqualIntegral 0 [c] [c'] a scale D
  obtain ⟨σ, hσ⟩ := ArchimedeanComplexPairFactor.complexLFactor_ne_zero (complexPairBlocks [c] [c'])
  have hpos (s : ℂ) (hs : -d.exponent.re < s.re) : 0 < (s + d.exponent).re := by
    rw [Complex.add_re]
    linarith
  constructor
  · rintro ⟨W, V, Φ⟩
    obtain ⟨Cw, hW⟩ := exists_eq_of_mem_complexWhittakerModel W.2
    obtain ⟨Cv, hV⟩ := exists_eq_of_mem_complexWhittakerModel V.2
    obtain ⟨Q, hQ⟩ := exists_polynomialGaussian_eq_lineSchwartz Φ.2
    obtain ⟨p, _, hp⟩ := complexTatePolynomialGaussian Q d.weight
    let k := (κ : ℂ) / 2 * (Cw * Cv)
    let q := Polynomial.C k * p.comp (Polynomial.X + Polynomial.C d.exponent)
    have hN (s : ℂ) : q.eval s = k * (Langlands.LocalFactor.ComplexTate.normalizedZeta
        (lineSchwartz Φ.val) d.weight (s + d.exponent)) := by
      rw [hQ, hp]
      simp only [q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X]
    refine ⟨q, ⟨q.eval, fun s _ => q.differentiable.analyticAt s, ⟨max σ (-d.exponent.re), fun s hs => ?_⟩⟩,
      fun _ => rfl⟩
    have hL : L.denominator s ≠ 0 := hσ s ((le_max_left _ _).trans_lt hs)
    have hRight := hpos s ((le_max_right _ _).trans_lt hs)
    have heq : q.eval s = J (W, V, Φ) s * L.denominator s := by
      change q.eval s = complexEqualIntegral D W V Φ.val s * (complexPairLFactor [c] [c']).denominator s
      rw [hN, normalizedZeta_eq_right _ _ hRight, equalIntegral_eq c c' hκ hW hV Φ.val,
        complexPairLFactor_singleton, zeta_shift, ← add_assoc]
      dsimp only [k, d]
      ring
    rw [heq, mul_assoc, mul_inv_cancel₀ hL, mul_one]
  · intro hM hM'
    obtain ⟨W, hW, hW₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    obtain ⟨V, hV, hV₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM'
    obtain ⟨Cw, hCw⟩ := exists_eq_of_mem_complexWhittakerModel hW
    obtain ⟨Cv, hCv⟩ := exists_eq_of_mem_complexWhittakerModel hV
    have hCw₀ : Cw ≠ 0 := fun h => hW₀ (funext fun g => by simp [hCw g, h])
    have hCv₀ : Cv ≠ 0 := fun h => hV₀ (funext fun g => by simp [hCv g, h])
    let k := (κ : ℂ) / 2 * (Cw * Cv)
    have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0
    have hk : k ≠ 0 := mul_ne_zero (div_ne_zero hκC two_ne_zero) (mul_ne_zero hCw₀ hCv₀)
    let Ψ := k⁻¹ • gaussSchwartz d.weight
    let Φ : {f : 𝓢(Row, ℂ) // IsGaussianPolynomialRow scale f} :=
      ⟨lineLift Ψ, isGaussianPolynomialRow_lineLift_gaussSchwartz k⁻¹ d.weight⟩
    have hΨ : (Ψ : ℂ → ℂ) = fun z => k⁻¹ * gaussian d.weight z := by
      funext z
      simp [Ψ, smul_eq_mul, gaussSchwartz_apply]
    let i : GaussianEqualTest 0 [c] [c'] a scale := (⟨W, hW⟩, ⟨V, hV⟩, Φ)
    refine ⟨i, ⟨fun _ => 1, fun _ _ => analyticAt_const, ⟨-d.exponent.re, fun s hs => ?_⟩⟩, fun _ => rfl⟩
    change complexEqualIntegral D W V Φ.val s = 1 * (L.denominator s)⁻¹
    have hΦ : lineSchwartz Φ.val = Ψ := lineSchwartz_lineLift Ψ
    rw [equalIntegral_eq c c' hκ hCw hCv Φ.val, hΦ, hΨ, complexPairLFactor_singleton,
      one_mul, inv_inv, ← add_assoc, zeta_shift,
      Langlands.LocalFactor.ComplexTate.zeta_const_mul, zeta_gaussian d.weight (hpos s hs)]
    change k * (k⁻¹ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀ hk, one_mul]

end Langlands.Global.RankinSelbergGlobal.ComplexRankZero
