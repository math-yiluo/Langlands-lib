import Langlands.Global.RankinSelberg.ComplexGodementTestDerivative
import Langlands.Analysis.CompactLinearParameterIntegralProof
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # The right Lie derivative of a compact Godement standard section -/

noncomputable section
open Filter MeasureTheory Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean (matrixModel rightDerivative rightDerivative_eq_fderiv unitsExtension
  unitsExtension_val differentiableAt_unitsExtension matrixExponentialGL matrixExponentialGL_coe)
open Langlands.Archimedean.MatrixGroupDifferentiation (matrixExponentialGL_zero continuous_matrixExponentialGL)
open Langlands.GeneralLinear (determinant determinantContinuous)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz operatorToEntry operatorToEntry_apply)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (contDiffAt_ofReal_cpow)
open ComplexGodementContinuedSmooth (testDerivative)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

section MatrixCurve

variable {n : ℕ}
local notation "GL" => Langlands.GeneralLinear n ℂ
local notation "Square" => Matrix (Fin n) (Fin n) ℂ

/-- Right translation by a one-parameter matrix subgroup. -/
def rightExponential (g : GL) (X : Square) (t : ℝ) : GL :=
  g * matrixExponentialGL ℂ n (t • X)

@[simp] theorem rightExponential_zero (g : GL) (X : Square) : rightExponential g X 0 = g := by
  simp [rightExponential]

theorem continuous_rightExponential (g : GL) (X : Square) : Continuous (rightExponential g X) :=
  continuous_const.mul (continuous_matrixExponentialGL.comp (continuous_id.smul continuous_const))

theorem hasDerivAt_rightExponential_val (g : GL) (X : Square) (t : ℝ) :
    HasDerivAt (fun u => (rightExponential g X u).val) ((rightExponential g X t).val * X) t := by
  simpa only [rightExponential, Units.val_mul, matrixExponentialGL_coe, mul_assoc] using
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).const_mul g.val

/-- The source right derivative is the scalar derivative along the matrix exponential. -/
theorem hasDerivAt_rightDerivative_exponential {f : GL → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (g : GL) (X : Square) :
    HasDerivAt (fun t => f (rightExponential g X t)) (rightDerivative (matrixModel ℂ n) X f g) 0 := by
  have hD := (differentiableAt_unitsExtension hf (rightExponential g X 0).isUnit).hasFDerivAt
  have hE := hasDerivAt_rightExponential_val g X 0
  have h := hD.comp_hasDerivAt (0 : ℝ) hE
  rw [rightDerivative_eq_fderiv hf]
  simpa only [Function.comp_def, unitsExtension_val, rightExponential_zero] using h

private def weightOnComplex (d : ComplexCharacterData) (s : ℂ) (z : ℂ) : ℂ :=
  (z / (‖z‖ : ℂ)) ^ d.weight * (‖z‖ : ℂ) ^ (2 * d.exponent) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s

private theorem differentiableAt_weightOnComplex (d : ComplexCharacterData) (s : ℂ) {z : ℂ}
    (hz : z ≠ 0) : DifferentiableAt ℝ (weightOnComplex d s) z := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz
  have hnc : DifferentiableAt ℝ (fun w : ℂ => (‖w‖ : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (hn.differentiableAt (by simp))
  have hu : DifferentiableAt ℝ (fun w : ℂ => w / (‖w‖ : ℂ)) z := by
    simp only [div_eq_mul_inv]
    exact (differentiableAt_id (𝕜 := ℝ) (x := z)).mul
      (hnc.inv (Complex.ofReal_ne_zero.mpr hp.ne'))
  have hunit : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz (Complex.ofReal_ne_zero.mpr hp.ne')
  have hw : DifferentiableAt ℂ (fun w : ℂ => w ^ d.weight) (z / (‖z‖ : ℂ)) :=
    (differentiableAt_zpow (m := d.weight)).2 (Or.inl hunit)
  exact (((hw.restrictScalars ℝ).comp z hu).mul
    ((contDiffAt_ofReal_cpow hn hp _).differentiableAt (by simp))).mul
      ((contDiffAt_ofReal_cpow (hn.pow 2) (pow_pos hp _) _).differentiableAt (by simp))

private theorem weightOnComplex_unit (d : ComplexCharacterData) (s : ℂ) (z : ℂˣ) :
    weightOnComplex d s z.val = characterWeight d s z := by
  change _ = (d.character z : ℂ) * normPower s z
  rw [d.character_eq]
  rfl

/-- The derivative at the identity of the determinant factor on the one-parameter subgroup. -/
def determinantSlope (d : ComplexCharacterData) (s : ℂ) (X : Square) : ℂ :=
  deriv (fun t : ℝ => characterWeight d s (determinant (matrixExponentialGL ℂ n (t • X)))) 0

private theorem hasDerivAt_weight_exponential (d : ComplexCharacterData) (s : ℂ) (X : Square) :
    HasDerivAt (fun t : ℝ => characterWeight d s (determinant (matrixExponentialGL ℂ n (t • X))))
      (determinantSlope d s X) 0 := by
  apply DifferentiableAt.hasDerivAt
  simp_rw [← weightOnComplex_unit]
  let Z (t : ℝ) := (NormedSpace.exp (t • X)).det
  change DifferentiableAt ℝ (fun t => weightOnComplex d s (Z t)) 0
  have hdet : Differentiable ℝ (fun Y : Square => Y.det) :=
    Langlands.Archimedean.ComplexMaximalParabolicIntegration.contDiff_det.differentiable (by simp)
  have hZ : DifferentiableAt ℝ Z 0 :=
    (hdet _).comp (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).differentiableAt
  have h0 : Z 0 ≠ 0 := by simp [Z]
  exact (differentiableAt_weightOnComplex d s h0).comp 0 hZ

/-- The determinant factor on a right exponential curve uses the same scalar derivative at
all base group elements. -/
theorem hasDerivAt_weight_rightExponential (d : ComplexCharacterData) (s : ℂ) (g : GL) (X : Square) :
    HasDerivAt (fun t => characterWeight d s (determinant (rightExponential g X t)))
      (characterWeight d s (determinant g) * determinantSlope d s X) 0 := by
  simp only [rightExponential, map_mul]
  exact (hasDerivAt_weight_exponential d s X).const_mul _

end MatrixCurve

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Square" => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Square₀" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Test" => OperatorSchwartz (r + 1) (r + 1 + 1)

private def trailingRowsLinear : Square →ₗ[ℝ] Rect where
  toFun := trailingRows
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def parameterLinear : Square₀ →ₗ[ℝ] (Square →L[ℝ] Rect) where
  toFun h := ((mulLeftLinearMap (Fin (r + 1 + 1)) ℝ h).comp trailingRowsLinear).toContinuousLinearMap
  map_add' h k := by
    ext Y i j
    change ((h + k) * trailingRows Y) i j = (h * trailingRows Y + k * trailingRows Y) i j
    rw [Matrix.add_mul]
  map_smul' c h := by
    ext Y i j
    change ((c • h) * trailingRows Y) i j = (c • (h * trailingRows Y)) i j
    rw [Matrix.smul_mul]

private theorem parameterLinear_mul_right (h : Square₀) (Y X : Square) :
    parameterLinear h (Y * X) = parameterLinear h Y * X := by
  change h * trailingRows (Y * X) = (h * trailingRows Y) * X
  rw [show trailingRows (Y * X) = trailingRows Y * X from
    Matrix.submatrix_mul Y X Fin.succ id id Function.bijective_id, Matrix.mul_assoc]

open scoped Matrix.Norms.Elementwise in
set_option maxHeartbeats 1300000 in
private theorem hasDerivAt_godementSection_integral (ν : Measure G) [IsLocallyFiniteMeasure ν]
    (d : ComplexCharacterData) (Φ : Test) (hΦ : HasCompactSupport Φ)
    (hfull : ∀ Y ∈ tsupport Φ, HasFullRowRank Y) {f : G → ℂ} (hf : Continuous f) (g : G') (X : Square) :
    HasDerivAt (fun t => ∫ h, godementSectionIntegrand d Φ f (rightExponential g X t) h ∂ν)
      (∫ h, godementSectionIntegrand d (operatorTestDerivative Φ X) f g h ∂ν) 0 := by
  let : SeminormedAddCommGroup Square := Matrix.linftyOpSeminormedAddCommGroup
  let : NormedAddCommGroup Square := Matrix.linftyOpNormedAddCommGroup
  let : NormedSpace ℝ Square := Matrix.linftyOpNormedSpace
  let Ψ := operatorTestDerivative Φ X
  let Φₑ := operatorToEntry Φ
  obtain ⟨L, hL, hLg⟩ := exists_compact_mem_nhds g
  obtain ⟨H₀, hH₀, hzero₀⟩ := exists_compact_godementSection_support hΦ hfull hL
  obtain ⟨hΨ, hΨf⟩ := operatorTestDerivative_support Φ X hΦ hfull
  obtain ⟨H₁, hH₁, hzero₁⟩ := exists_compact_godementSection_support hΨ hΨf hL
  let H := H₀ ∪ H₁
  have hH := hH₀.union hH₁
  let c (h : G) := f h⁻¹ * characterWeight d ((((r + 1 : ℕ) : ℂ) + 1) / 2) (determinant h)
  have hc : Continuous c := (hf.comp continuous_inv).mul
    ((continuous_characterWeight d _).comp determinantContinuous.continuous)
  let A (h : G) : Square →L[ℝ] Rect := parameterLinear h.val
  have hA : Continuous A := parameterLinear.toContinuousLinearMap.continuous.comp Units.continuous_val
  let Q (h : G) : Square →L[ℝ] ℂ := c h • ((fderiv ℝ (Φₑ : Rect → ℂ) (A h g.val)).comp (A h))
  have hQ : Continuous Q := hc.smul
    ((((Φₑ.smooth ⊤).continuous_fderiv (by simp)).comp (hA.clm_apply continuous_const)).clm_comp hA)
  have hQi : Integrable Q (ν.restrict H) := hQ.continuousOn.integrableOn_compact hH
  have hD := (Langlands.Analysis.compactLinearParameterIntegral G Square Rect ν H hH
    univ isOpen_univ univ isOpen_univ c hc A hA Φₑ ((Φₑ.smooth ⊤).contDiffOn)
    (fun _ _ _ _ => mem_univ _)).2 (rightExponential g X 0).val (mem_univ _)
  have hExp := hasDerivAt_rightExponential_val g X 0
  have hDerivative := hD.comp_hasDerivAt (0 : ℝ) hExp
  simp only [rightExponential_zero] at hDerivative
  change HasDerivAt (fun t => ∫ h in H, c h * Φₑ (A h (rightExponential g X t).val) ∂ν)
    ((∫ h in H, Q h ∂ν) (g.val * X)) 0 at hDerivative
  have hEval : (∫ h in H, Q h ∂ν) (g.val * X) = ∫ h, godementSectionIntegrand d Ψ f g h ∂ν := by
    rw [ContinuousLinearMap.integral_apply hQi]
    calc
      _ = ∫ h in H, godementSectionIntegrand d Ψ f g h ∂ν := by
        apply integral_congr_ae
        refine ae_of_all _ fun h => ?_
        change c h * fderiv ℝ (Φₑ : Rect → ℂ) (A h g.val) (A h (g.val * X)) =
          Ψ (A h g.val) * f h⁻¹ * characterWeight d ((((r + 1 : ℕ) : ℂ) + 1) / 2) (determinant h)
        have hAX : A h (g.val * X) = A h g.val * X := parameterLinear_mul_right h.val g.val X
        rw [hAX]
        change c h * fderiv ℝ (Φₑ : Rect → ℂ) (A h g.val) (A h g.val * X) =
          testDerivative Φₑ X (A h g.val) * f h⁻¹ * characterWeight d _ (determinant h)
        rw [testDerivative_apply]
        dsimp only [c]
        ring
      _ = _ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro h hh
        have hz := hzero₁ g (mem_of_mem_nhds hLg) h (fun hb => hh (Or.inr hb))
        rw [godementSectionIntegrand, hz, zero_mul, zero_mul]
  rw [hEval] at hDerivative
  apply hDerivative.congr_of_eventuallyEq
  have hnear : ∀ᶠ t in 𝓝 0, rightExponential g X t ∈ L :=
    (continuous_rightExponential g X).continuousAt.eventually (by simpa using hLg)
  filter_upwards [hnear] with t ht
  symm
  calc
    _ = ∫ h, c h * Φₑ (A h (rightExponential g X t).val) ∂ν := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro h hh
      change c h * Φ (h.val * trailingRows (rightExponential g X t).val) = 0
      rw [hzero₀ _ ht h (fun hb => hh (Or.inl hb)), mul_zero]
    _ = _ := by
      apply integral_congr_ae
      refine ae_of_all _ fun h => ?_
      change c h * Φ (h.val * trailingRows (rightExponential g X t).val) =
        godementSectionIntegrand d Φ f (rightExponential g X t) h
      unfold godementSectionIntegrand
      dsimp only [c]
      ring

/-- The right Lie derivative is the sum of the determinant slope times the original section
and the section with the differentiated test. -/
theorem rightDerivative_godementSection (ν : Measure G) [IsLocallyFiniteMeasure ν]
    (d : ComplexCharacterData) (Φ : Test) (hΦ : HasCompactSupport Φ)
    (hfull : ∀ Y ∈ tsupport Φ, HasFullRowRank Y) {f : G → ℂ} (hf : Continuous f) (X : Square) :
    rightDerivative (matrixModel ℂ (r + 1 + 1)) X (godementSection ν d Φ f) =
      determinantSlope d (((r + 1 : ℕ) : ℂ) / 2) X • godementSection ν d Φ f +
        godementSection ν d (operatorTestDerivative Φ X) f := by
  funext g
  have hs := hasDerivAt_rightDerivative_exponential
    (contMDiff_godementSection ν d (Φ.smooth ⊤) hΦ hfull hf) g X
  have h := (hasDerivAt_weight_rightExponential d (((r + 1 : ℕ) : ℂ) / 2) g X).mul
    (hasDerivAt_godementSection_integral ν d Φ hΦ hfull hf g X)
  have he := h.deriv
  change deriv (fun t => godementSection ν d Φ f (rightExponential g X t)) 0 = _ at he
  rw [← hs.deriv, he, rightExponential_zero]
  simp only [godementSection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable (r) in
/-- Right differentiation along a real matrix direction acts on the compact Godement section
by differentiating the test and multiplying by the derivative of the determinant character. -/
def ComplexGodementStandardLieStatement : Prop :=
  ∀ (ν : Measure G) [IsLocallyFiniteMeasure ν] (d : ComplexCharacterData) (Φ : Test),
    HasCompactSupport Φ → (∀ Y ∈ tsupport Φ, HasFullRowRank Y) →
    ∀ (f : G → ℂ), Continuous f → ∀ (X : Square),
      rightDerivative (matrixModel ℂ (r + 1 + 1)) X (godementSection ν d Φ f) =
        determinantSlope d (((r + 1 : ℕ) : ℂ) / 2) X • godementSection ν d Φ f +
          godementSection ν d (operatorTestDerivative Φ X) f

theorem complexGodementStandardLie : ComplexGodementStandardLieStatement r := by
  intro ν hν d Φ hΦ hfull f hf X
  exact rightDerivative_godementSection ν d Φ hΦ hfull hf X

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
