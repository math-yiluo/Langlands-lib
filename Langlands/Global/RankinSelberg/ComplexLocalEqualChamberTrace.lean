import Langlands.Global.RankinSelberg.ComplexLocalAdjoiningShift
import Langlands.Global.RankinSelberg.ComplexLocalEqualProductConvergence

/-! # Square-test trace estimates and holomorphy on the joint convergence chamber -/

noncomputable section

open MeasureTheory Filter
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGodement (shiftedCharacter)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Test" => 𝓢(Mat, ℂ)

private theorem norm_kernel_le_endpoints (d₁ d₂ d : ComplexCharacterData)
    (h₁ : d₁.exponent.re ≤ d.exponent.re) (h₂ : d.exponent.re ≤ d₂.exponent.re)
    (Φ : Mat → ℂ) (U : H → ℂ) (V : G → ℂ) (s : ℂ) (q : Q × G) :
    ‖complexEqualUnfoldedKernel d Φ U V s q‖ ≤
      ‖complexEqualUnfoldedKernel d₁ Φ U V s q‖ + ‖complexEqualUnfoldedKernel d₂ Φ U V s q‖ := by
  let g := determinant q.2
  rcases le_total 1 ‖(g : ℂ)‖ with hg | hg
  · have hchar : ‖(d.character g : ℂ)‖ ≤ ‖(d₂.character g : ℂ)‖ := by
      rw [ComplexSwapJacquet.norm_character, ComplexSwapJacquet.norm_character]
      exact Real.rpow_le_rpow_of_exponent_le hg (by linarith)
    refine le_trans ?_ (le_add_of_nonneg_left (norm_nonneg _))
    simp only [complexEqualUnfoldedKernel, norm_mul]
    gcongr
  · have hchar : ‖(d.character g : ℂ)‖ ≤ ‖(d₁.character g : ℂ)‖ := by
      rw [ComplexSwapJacquet.norm_character, ComplexSwapJacquet.norm_character]
      exact Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr g.ne_zero) hg (by linarith)
    refine le_trans ?_ (le_add_of_nonneg_right (norm_nonneg _))
    simp only [complexEqualUnfoldedKernel, norm_mul]
    gcongr

/-- The iterated unfolded integral is the integral of the joint product kernel. -/
theorem complexEqualUnfoldedIntegral_eq_prod (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (μ : Measure G) [SFinite μ] (d : ComplexCharacterData) (Φ : Test) (U : H → ℂ) (V : G → ℂ)
    (s : ℂ) (h : Integrable (complexEqualUnfoldedKernel d Φ U V s) (D.measure.prod μ)) :
    complexEqualUnfoldedIntegral μ D d.character.toMonoidHom Φ U V s =
      ∫ q, complexEqualUnfoldedKernel d Φ U V s q ∂D.measure.prod μ := by
  rw [integral_prod_symm _ h]
  unfold complexEqualUnfoldedIntegral complexEqualUnfoldedKernel
  simp only [integral_const_mul, ContinuousMonoidHom.coe_toMonoidHom]
  rfl

/-- At a fixed spectral real part, a compact interval in the adjoining positive
chamber gives a continuous square-test bound, uniform in both imaginary parts. -/
def ComplexLocalEqualChamberTraceStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure] (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    (a : ℂˣ) (ds es : List ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a)),
  ∃ (T σ : ℝ), ∀ (d₁ d₂ : ComplexCharacterData) (t : ℝ),
    T ≤ d₁.exponent.re → T ≤ d₂.exponent.re → σ < t →
    ∃ weight : Test → ℝ, Continuous weight ∧ weight 0 = 0 ∧
      ∀ (Φ : Test) (d : ComplexCharacterData) (s : ℂ),
        d₁.exponent.re ≤ d.exponent.re → d.exponent.re ≤ d₂.exponent.re → s.re = t →
        Integrable (complexEqualUnfoldedKernel d Φ U.val V.val s) (D.measure.prod μ) ∧
        ‖complexEqualUnfoldedIntegral μ D d.character.toMonoidHom Φ U.val V.val s‖ ≤ weight Φ

theorem complexLocalEqualChamberTrace : ComplexLocalEqualChamberTraceStatement (r := r) := by
  intro D _ μ _ _ a ds es U V
  obtain ⟨T, σ, h⟩ := complexLocalEqualProductTrace D μ a ds es U V
  refine ⟨T, σ, fun d₁ d₂ t h₁ h₂ ht => ?_⟩
  have ht' : σ < (t : ℂ).re := by simpa only [Complex.ofReal_re] using ht
  obtain ⟨p₁, hp₁, hz₁, hb₁⟩ := h d₁ t h₁ ht'
  obtain ⟨p₂, hp₂, hz₂, hb₂⟩ := h d₂ t h₂ ht'
  refine ⟨fun Φ => p₁ Φ + p₂ Φ, hp₁.add hp₂, by simp [hz₁, hz₂],
    fun Φ d s hd₁ hd₂ hs => ?_⟩
  have hs' : σ < s.re := hs ▸ ht
  obtain ⟨_, _, _, hb⟩ := h d s (h₁.trans hd₁) hs'
  have hi := (hb Φ d s rfl rfl).1
  have hi₁ := hb₁ Φ d₁ s rfl (hs.trans (Complex.ofReal_re t).symm)
  have hi₂ := hb₂ Φ d₂ s rfl (hs.trans (Complex.ofReal_re t).symm)
  refine ⟨hi, ?_⟩
  rw [complexEqualUnfoldedIntegral_eq_prod D μ d Φ U.val V.val s hi]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_ae hi.norm (hi₁.1.norm.add hi₂.1.norm)
    (.of_forall (norm_kernel_le_endpoints d₁ d₂ d hd₁ hd₂ Φ U.val V.val s))).trans ?_
  rw [Pi.add_def, integral_add hi₁.1.norm hi₂.1.norm]
  exact add_le_add hi₁.2 hi₂.2

/-- On the common absolute-convergence region the unfolded integral is
holomorphic along every real-slope affine line in its two exponents. -/
theorem differentiableOn_complexEqualUnfoldedIntegral_affine
    (D : ComplexQuotientMeasureData r) [SFinite D.measure] (μ : Measure G) [SFinite μ]
    (d : ComplexCharacterData) (Φ : Test) (U : H → ℂ) (V : G → ℂ)
    (u₀ s₀ : ℂ) (c₁ c₂ : ℝ) {S : Set ℂ} (hS : IsOpen S)
    (hInt : ∀ t ∈ S,
      Integrable (complexEqualUnfoldedKernel (shiftedCharacter d (u₀ + (c₁ : ℂ) * t)) Φ U V
        (s₀ + (c₂ : ℂ) * t)) (D.measure.prod μ)) :
    DifferentiableOn ℂ (fun t =>
      complexEqualUnfoldedIntegral μ D (shiftedCharacter d (u₀ + (c₁ : ℂ) * t)).character.toMonoidHom
        Φ U V (s₀ + (c₂ : ℂ) * t)) S := by
  let A := complexEqualUnfoldedKernel (shiftedCharacter d u₀) Φ U V s₀
  let Lg (g : G) := Real.log (complexNormalizedAbs g.val.det)
  let L (q : Q × G) := (c₁ + c₂) * Lg q.2 + c₂ * complexQuotientLogDet q.1
  have hLg : Measurable Lg :=
    ((Units.continuous_val.matrix_det.norm.pow 2).measurable).log
  have hL : Measurable L :=
    (hLg.comp measurable_snd |>.const_mul _).add
      ((continuous_complexQuotientLogDet.measurable.comp measurable_fst).const_mul _)
  have hEq (t : ℂ) (q : Q × G) :
      complexEqualUnfoldedKernel (shiftedCharacter d (u₀ + (c₁ : ℂ) * t)) Φ U V (s₀ + (c₂ : ℂ) * t) q =
        A q * Complex.exp (t * (L q : ℂ)) := by
    dsimp only [A, L, Lg, complexEqualUnfoldedKernel, complexEqualUnfoldedInner]
    rw [shiftedCharacter_det_apply, shiftedCharacter_det_apply, complexQuotientLogDet_out]
    unfold ArchimedeanLocal.detPower
    push_cast
    simp only [add_mul, sub_mul, mul_add, Complex.exp_add, Complex.exp_sub]
    ring_nf
  have hIt (t : ℂ) (ht : t ∈ S) : Integrable (fun q => A q * Complex.exp (t * (L q : ℂ)))
      (D.measure.prod μ) := (hInt t ht).congr (.of_forall (hEq t))
  refine (differentiableOn_integral_mul_cexp hL hS hIt).congr ?_
  intro t ht
  rw [complexEqualUnfoldedIntegral_eq_prod D μ _ Φ U V _ (hInt t ht)]
  exact integral_congr_ae (.of_forall (hEq t))

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
