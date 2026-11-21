import Langlands.Global.RankinSelberg.ComplexLocalEqualFiniteSquareChambers
import Langlands.LocalFactor.Archimedean.GammaStripGrowth

/-! # Vertical line estimates for differences of normalized square traces -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGodement (shiftedCharacter shiftedCharacter_exponent)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Test" => 𝓢(Mat, ℂ)

private theorem norm_le_all_strip_of_stripGrowth {F : ℂ → ℂ} (hF : Continuous F)
    (h : HasStripExponentialGrowth F) (l u : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖F z‖ ≤ C * Real.exp (K * |z.im|) := by
  obtain ⟨C, K, T, hC, hK, h⟩ := h l u
  let A := max T 0
  have hRect := (isCompact_Icc (a := l) (b := u)).reProdIm (isCompact_Icc (a := -A) (b := A))
  obtain ⟨M, hM⟩ := hRect.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C M, K, hC.trans (le_max_left _ _), hK, fun z hz₁ hz₂ => ?_⟩
  by_cases ht : T ≤ |z.im|
  · exact (h z hz₁ hz₂ ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have him : |z.im| ≤ A := (lt_of_not_ge ht).le.trans (le_max_left _ _)
    have hb := hM z (Complex.mem_reProdIm.mpr ⟨⟨hz₁, hz₂⟩, abs_le.mp him⟩)
    calc
      ‖F z‖ ≤ max C M := hb.trans (le_max_right _ _)
      _ ≤ max C M * Real.exp (K * |z.im|) :=
        le_mul_of_one_le_right (hC.trans (le_max_left _ _)) (Real.one_le_exp (by positivity))

private theorem unfolded_sub (D₁ : ComplexQuotientMeasureData r) [SFinite D₁.measure]
    (μ : Measure G) [SFinite μ] (d : ComplexCharacterData) (Φ Ψ : Test)
    (U : H → ℂ) (V : G → ℂ) (s : ℂ)
    (hΦ : Integrable (complexEqualUnfoldedKernel d Φ U V s) (D₁.measure.prod μ))
    (hΨ : Integrable (complexEqualUnfoldedKernel d Ψ U V s) (D₁.measure.prod μ)) :
    complexEqualUnfoldedIntegral μ D₁ d.character.toMonoidHom Φ U V s -
      complexEqualUnfoldedIntegral μ D₁ d.character.toMonoidHom Ψ U V s =
    complexEqualUnfoldedIntegral μ D₁ d.character.toMonoidHom (Φ - Ψ : Test) U V s := by
  have hk : complexEqualUnfoldedKernel d (Φ - Ψ : Test) U V s =
      complexEqualUnfoldedKernel d Φ U V s - complexEqualUnfoldedKernel d Ψ U V s := by
    funext q
    simp only [complexEqualUnfoldedKernel, Pi.sub_apply]
    change (Φ q.2.val - Ψ q.2.val) * _ * _ * _ = _
    ring
  have hSub : Integrable (complexEqualUnfoldedKernel d (Φ - Ψ : Test) U V s) (D₁.measure.prod μ) := by
    rw [hk]
    exact hΦ.sub hΨ
  have hProd (Φ : Test) (h : Integrable (complexEqualUnfoldedKernel d Φ U V s) (D₁.measure.prod μ)) :=
    complexEqualUnfoldedIntegral_eq_prod D₁ μ d (complexMatrixEntryToOperator Φ) U V s (by
      rw [coe_complexMatrixEntryToOperator]
      exact h)
  have hProd' (Φ : Test) (h : Integrable (complexEqualUnfoldedKernel d Φ U V s) (D₁.measure.prod μ)) :
      complexEqualUnfoldedIntegral μ D₁ d.character.toMonoidHom Φ U V s =
        ∫ q, complexEqualUnfoldedKernel d Φ U V s q ∂D₁.measure.prod μ := by
    simpa only [coe_complexMatrixEntryToOperator] using hProd Φ h
  rw [hProd' Φ hΦ, hProd' Ψ hΨ, hProd' (Φ - Ψ) hSub, hk]
  simp only [Pi.sub_apply, integral_sub hΦ hΨ]

/-- The normalized double integral at a shifted adjoining character. -/
def complexEqualNormalizedSquareTrace (D₁ : ComplexQuotientMeasureData r) (μ : Measure G)
    (d : ComplexCharacterData) (ds es : List ComplexCharacterData) (c : ℂ)
    (U : H → ℂ) (V : G → ℂ) (Φ : Test) (z s : ℂ) : ℂ :=
  c * (equalDoubleDenominator d ds es z s *
    complexEqualUnfoldedIntegral μ D₁ (shiftedCharacter d z).character.toMonoidHom Φ U V s)

/-- On a fixed spectral line and a bounded interval of real shifts, differences
of normalized square traces are weighted by a continuous function of the test difference. -/
theorem exists_complexEqualNormalizedSquareTrace_bound
    (D₁ : ComplexQuotientMeasureData r) [SFinite D₁.measure] (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    (d : ComplexCharacterData) (a : ℂˣ) (ds es : List ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (xs ys : List ComplexCharacterData) (c : ℂ) :
    ∃ τ σ : ℝ, ∀ l u t : ℝ, τ < l → l ≤ u → σ < t →
      ∃ (K L : ℝ) (p : Test → ℝ), 0 ≤ K ∧ 0 ≤ L ∧ Continuous p ∧ p 0 = 0 ∧
        ∀ (Φ Ψ : Test) (z s : ℂ), l ≤ z.re → z.re ≤ u → s.re = t →
          ‖complexEqualNormalizedSquareTrace D₁ μ d xs ys c U.val V.val Φ z s -
            complexEqualNormalizedSquareTrace D₁ μ d xs ys c U.val V.val Ψ z s‖ ≤
            p (Φ - Ψ) * Real.exp (K * |s.im| + L * |z.im|) := by
  obtain ⟨T, σ, h⟩ := complexLocalEqualChamberTrace D₁ μ a ds es U V
  refine ⟨T - d.exponent.re, σ, fun l u t hl hlu ht => ?_⟩
  have hreal (z : ℂ) : (shiftedCharacter d z).exponent.re = d.exponent.re + z.re := by
    rw [shiftedCharacter_exponent, Complex.add_re]
  have h₁ : T ≤ (shiftedCharacter d (l : ℂ)).exponent.re := by
    rw [hreal, Complex.ofReal_re]
    linarith
  have h₂ : T ≤ (shiftedCharacter d (u : ℂ)).exponent.re := by
    rw [hreal, Complex.ofReal_re]
    linarith
  obtain ⟨p, hp, hp₀, hP⟩ := h (shiftedCharacter d l) (shiftedCharacter d u) t h₁ h₂ ht
  let P : Test → Langlands.Analysis.SchwartzMatrixNorm.OperatorSchwartz n n :=
    complexMatrixEntryToOperator
  have hPcont : Continuous P := ContinuousLinearMap.continuous _
  have hPzero : P 0 = 0 := by
    dsimp only [P, complexMatrixEntryToOperator]
    exact map_zero _
  obtain ⟨C, K, hC, hK, hF₁⟩ := norm_le_all_strip_of_stripGrowth
    (complexPairLFactor ys xs).entire.continuous
      (stripGrowth_complexPairLFactor_denominator ys xs) t t
  obtain ⟨E, L, hE, hL, hF₂⟩ := norm_le_all_strip_of_stripGrowth
    (complexPairLFactor [d] ys).entire.continuous
      (stripGrowth_complexPairLFactor_denominator [d] ys) (t + l) (t + u)
  let M := ‖c‖ * (C * E)
  refine ⟨K + L, L, fun Ψ => M * p (P Ψ), add_nonneg hK hL, hL, (hp.comp hPcont).const_mul _,
    by simp only [hPzero, hp₀, mul_zero], fun Φ Ψ z s hz₁ hz₂ hs => ?_⟩
  let e := shiftedCharacter d z
  have hdz₁ : (shiftedCharacter d (l : ℂ)).exponent.re ≤ e.exponent.re := by
    rw [hreal, hreal, Complex.ofReal_re]
    linarith
  have hdz₂ : e.exponent.re ≤ (shiftedCharacter d (u : ℂ)).exponent.re := by
    rw [hreal, hreal, Complex.ofReal_re]
    linarith
  have hRaw (Φ : Test) := hP (P Φ) e s hdz₁ hdz₂ hs
  simp only [P, coe_complexMatrixEntryToOperator] at hRaw
  have hsub := unfolded_sub D₁ μ e Φ Ψ U.val V.val s (hRaw Φ).1 (hRaw Ψ).1
  have hF₂s := hF₂ (s + z) (by rw [Complex.add_re, hs]; gcongr) (by rw [Complex.add_re, hs]; gcongr)
  have hsum : |(s + z).im| ≤ |s.im| + |z.im| := by
    rw [Complex.add_im]
    exact abs_add_le _ _
  dsimp only [complexEqualNormalizedSquareTrace]
  rw [← mul_sub, ← mul_sub, hsub, equalDoubleDenominator]
  simp only [norm_mul]
  calc
    _ ≤ ‖c‖ * ((C * Real.exp (K * |s.im|)) *
        (E * Real.exp (L * (|s.im| + |z.im|))) * p (P (Φ - Ψ))) := by
      have hb₂ := hF₂s.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum hL)) hE)
      gcongr <;> first | exact hF₁ s hs.ge hs.le | exact hb₂ | exact (hRaw (Φ - Ψ)).2
    _ = _ := by
      dsimp only [M]
      rw [add_mul, mul_add L, Real.exp_add, Real.exp_add, Real.exp_add]
      ring

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
