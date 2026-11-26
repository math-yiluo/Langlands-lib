import Langlands.Global.RankinSelberg.ComplexGapSquareReflection
import Langlands.Global.RankinSelberg.ComplexGodementDilation
import Langlands.Global.RankinSelberg.ComplexSquareConvolutionSpan
import Langlands.Global.RankinSelberg.ComplexGapSeparatedKernels
import Langlands.Global.RankinSelberg.ComplexWeightedKernelReflection
import Langlands.Global.RankinSelberg.ArchimedeanStripGrowth
import Langlands.Analysis.MellinHalfPlaneProof
import Langlands.Analysis.LandauDirichlet

/-! # The normalized square convolution after a common scalar dilation -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap NNReal Topology Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSquareReflection

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean
open Langlands.GodementJacquet (complexMatrixHeight_inverseTranspose complexNormalizedAbs_det_pos)
open ComplexAdjacentUnfolding (splitSquareTransform dilateMatrixTest dilateMatrixTest_apply)
open ComplexCharacterChange (centralCharacter coe_centralCharacter model_mul_scalar complexMatrixHeight_mul_le)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSeparatedKernels (detPower_mul detPower_add)
open ComplexGodement (characterWeight continuous_characterWeight normPower)
open ComplexGodementPaddedRestriction (normPower_determinant)
open ComplexJacquet (HasSquareConvolutionTrace complexJacquetMatrixIntegrand complexWeightedMatrixTest
  complexLocalMatrixMajorant continuous_complexDeterminant continuous_complexDetPower complexMatrixHeight_nonneg)
open ComplexWeightedKernelReflection (pairReflectionFactor)
open Langlands.GeneralDirichlet (eqOn_halfPlane)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable (t : ℕ)
local notation "k" => (t + 1)
local notation "G" => Langlands.GeneralLinear k ℂ
local notation "K" => unitaryCompact ℂ k
local notation "Mat" => Matrix (Fin k) (Fin k) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "ι" => inverseTranspose k ℂ

private def squareDet (g : G) : ℝ := complexNormalizedAbs g.val.det

private theorem squareKernel_eq_matrixIntegrand (d : ComplexCharacterData) (Φ : Mat → ℂ) (b : G → ℂ)
    (s : ℂ) (g : G) : squareKernel d Φ b s g = complexJacquetMatrixIntegrand d b Φ s g := by
  change Φ g.val * ((d.character (determinant g) : ℂ) * normPower ((t : ℂ) / 2 + s) (determinant g)) * b g =
    Φ g.val * (d.character (determinant g) : ℂ) * P g (s + (t : ℂ) / 2) * b g
  rw [normPower_determinant, add_comm ((t : ℂ) / 2)]
  ring

private theorem squareKernel_spectral (d : ComplexCharacterData) (Φ : Mat → ℂ) (b : G → ℂ)
    (s : ℂ) (g : G) : squareKernel d Φ b s g = squareKernel d Φ b 0 g * (squareDet t g : ℂ) ^ s := by
  change Φ g.val * ((d.character (determinant g) : ℂ) * normPower ((t : ℂ) / 2 + s) (determinant g)) * b g =
    Φ g.val * ((d.character (determinant g) : ℂ) * normPower ((t : ℂ) / 2 + 0) (determinant g)) * b g *
      normPower s (determinant g)
  simp only [add_zero, normPower_determinant, detPower_add]
  ring

private theorem differentiableOn_right_mellin {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A : X → ℂ} {D : X → ℝ} (hA : AEStronglyMeasurable A μ) (hD : AEMeasurable D μ)
    (hpos : ∀ x, 0 < D x) (b : ℝ)
    (hI : ∀ r : ℝ, b < r → Integrable (fun x => A x * (D x : ℂ) ^ (r : ℂ)) μ) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x, A x * (D x : ℂ) ^ s ∂μ) {s : ℂ | b < s.re} := by
  have hm := Langlands.Analysis.mellinHalfPlane X μ A D (-b) hpos hA hD (fun r hr => by
    have h := hI (r + b) (by linarith)
    simpa only [Complex.ofReal_neg, sub_neg_eq_add, Complex.ofReal_add] using h)
  have h_aff : Differentiable ℂ (fun s : ℂ => s - (b : ℂ)) := differentiable_id.sub_const _
  have hmaps : MapsTo (fun s : ℂ => s - (b : ℂ)) {s : ℂ | b < s.re} {s : ℂ | 0 < s.re} := by
    intro z hz
    change 0 < (z - (b : ℂ)).re
    change b < z.re at hz
    simpa only [Complex.sub_re, Complex.ofReal_re, sub_pos] using hz
  simpa only [Function.comp_def, Complex.ofReal_neg, sub_neg_eq_add, sub_add_cancel] using
    hm.comp h_aff.differentiableOn hmaps

private theorem squareKernel_right (μ : Measure G) [μ.IsHaarMeasure] (d : ComplexCharacterData)
    (Φ : 𝓢(Mat, ℂ)) (b : G → ℂ) (hb : Continuous b) (N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ g, ‖b g‖ ≤ C * complexMatrixHeight g ^ N) :
    let τ := ((k : ℕ) : ℝ) + N - ((t : ℂ) / 2 + d.exponent).re
    (∀ s : ℂ, τ < s.re → Integrable (squareKernel d Φ b s) μ) ∧
      DifferentiableOn ℂ (fun s => ∫ g, squareKernel d Φ b s g ∂μ) {s : ℂ | τ < s.re} := by
  intro τ
  let A (s : ℂ) := complexWeightedMatrixTest d.character Φ (s + (t : ℂ) / 2)
  have he (s : ℂ) (g : G) : squareKernel d Φ b s g = A s g * b g :=
    squareKernel_eq_matrixIntegrand t d Φ b s g
  have hK (s : ℂ) : Continuous (squareKernel d Φ b s) := by
    rw [funext (he s)]
    exact (((Φ.continuous.comp Units.continuous_val).mul
      (Units.continuous_val.comp (d.character.continuous.comp continuous_complexDeterminant))).mul
        (continuous_complexDetPower _)).mul hb
  have hI (s : ℂ) (hs : τ < s.re) : Integrable (squareKernel d Φ b s) μ := by
    have hs' : ((k : ℕ) : ℝ) + N ≤ (s + (t : ℂ) / 2 + d.exponent).re := by
      rw [add_assoc, Complex.add_re]
      dsimp only [τ] at hs
      linarith
    have h := (complexLocalMatrixMajorant k N μ d Φ (s + (t : ℂ) / 2) hs').const_mul C
    refine h.mono' (hK s).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    change ‖squareKernel d Φ b s g‖ ≤ C * (max 1 (complexMatrixHeight g) ^ N * ‖A s g‖)
    rw [he, norm_mul]
    calc
      _ ≤ ‖A s g‖ * (C * max 1 (complexMatrixHeight g) ^ N) :=
        mul_le_mul_of_nonneg_left ((hB g).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (complexMatrixHeight_nonneg _) (le_max_right _ _) N) hC)) (norm_nonneg _)
      _ = _ := by ring
  refine ⟨hI, ?_⟩
  have hSpect : (fun s => ∫ g, squareKernel d Φ b s g ∂μ) =
      fun s => ∫ g, squareKernel d Φ b 0 g * (squareDet t g : ℂ) ^ s ∂μ := by
    funext s
    exact integral_congr_ae (ae_of_all _ (squareKernel_spectral t d Φ b s))
  rw [hSpect]
  have hδm : Measurable (squareDet t) := ((Units.continuous_val.matrix_det.norm).pow 2).measurable
  refine differentiableOn_right_mellin (hK 0).aestronglyMeasurable hδm.aemeasurable
    (fun g => complexNormalizedAbs_det_pos g) τ
    (fun u hu => ?_)
  have hs : τ < (u : ℂ).re := by simpa only [Complex.ofReal_re] using hu
  exact (hI (u : ℂ) hs).congr (ae_of_all _ (squareKernel_spectral t d Φ b (u : ℂ)))

/-- The scalar in the normalized square convolution when the test is evaluated on `u • X`. -/
def squareDilationWeight (d : ComplexCharacterData) (es : List ComplexCharacterData) (u : ℂˣ) (s : ℂ) : ℂ :=
  (centralCharacter es u⁻¹ : ℂ) * characterWeight d ((t : ℂ) / 2 + s) (determinant (scalar (n := k) u⁻¹))

/-- For a fixed dilation, the weight is entire in the spectral parameter. -/
theorem differentiable_squareDilationWeight (d : ComplexCharacterData) (es : List ComplexCharacterData) (u : ℂˣ) :
    Differentiable ℂ (squareDilationWeight t d es u) := by
  let z : G := scalar u⁻¹
  change Differentiable ℂ (fun w => (centralCharacter es u⁻¹ : ℂ) *
    ((d.character (determinant z) : ℂ) * normPower ((t : ℂ) / 2 + w) (determinant z)))
  simp only [normPower_determinant, ArchimedeanLocal.detPower]
  exact (((differentiable_id.const_add ((t : ℂ) / 2)).mul_const _).cexp.const_mul _).const_mul _

/-- For a fixed spectral value, the weight varies continuously in the dilation. -/
theorem continuous_squareDilationWeight (d : ComplexCharacterData) (es : List ComplexCharacterData) (s : ℂ) :
    Continuous (fun u => squareDilationWeight t d es u s) := by
  have hZ : Continuous (fun u : ℂˣ => (centralCharacter es u : ℂ)) := by
    simp_rw [coe_centralCharacter]
    exact continuous_list_prod es (fun e _ => Units.continuous_val.comp e.character.continuous)
  have hD : Continuous (fun u : ℂˣ => determinant (scalar (n := k) u⁻¹)) :=
    determinantContinuous.continuous.comp ((scalarContinuous (R := ℂ) (n := k)).continuous.comp continuous_inv)
  exact (hZ.comp continuous_inv).mul ((continuous_characterWeight d _).comp hD)

/-- The scalar weight for any fixed dilation has exponential strip growth. -/
theorem stripGrowth_squareDilationWeight (d : ComplexCharacterData) (es : List ComplexCharacterData) (u : ℂˣ) :
    HasStripExponentialGrowth (squareDilationWeight t d es u) := by
  let z : G := scalar u⁻¹
  let c := (centralCharacter es u⁻¹ : ℂ) * (d.character (determinant z) : ℂ)
  have h := (ArchimedeanInverseMellin.StripExpType.ofReal_cpow (complexNormalizedAbs_det_pos z)).comp_add ((t : ℂ) / 2)
  apply ArchimedeanInverseMellin.StripExpType.hasStripExponentialGrowth
  refine ((ArchimedeanInverseMellin.StripExpType.const c).mul h).congr fun s => ?_
  change c * (complexNormalizedAbs z.val.det : ℂ) ^ (s + (t : ℂ) / 2) =
    (centralCharacter es u⁻¹ : ℂ) * ((d.character (determinant z) : ℂ) *
      normPower ((t : ℂ) / 2 + s) (determinant z))
  dsimp only [c]
  rw [add_comm s, mul_assoc]
  rfl

/-- Dilation of a square test is a scalar multiplier of the Whittaker convolution. -/
theorem squareKernel_dilate_integral (μ : Measure G) [μ.IsMulLeftInvariant] (d : ComplexCharacterData)
    {es : List ComplexCharacterData} (hLen : es.length = k) {a : ℂˣ}
    {b : G → ℂ} (hb : b ∈ complexWhittakerModel t es a) (Φ : 𝓢(Mat, ℂ)) (u : ℂˣ) (s : ℂ) (x : G) :
    (∫ g, squareKernel d (dilateMatrixTest u Φ) (fun g => b (x * g)) s g ∂μ) =
      squareDilationWeight t d es u s * ∫ g, squareKernel d Φ (fun g => b (x * g)) s g ∂μ := by
  let z : G := scalar u
  let zi : G := scalar u⁻¹
  have hzi : zi = z⁻¹ := map_inv scalar u
  have hΦ (g : G) : (dilateMatrixTest u Φ) (zi * g).val = Φ g.val := by
    rw [dilateMatrixTest_apply]
    have hz (h : G) : (z * h).val = (u : ℂ) • h.val := by
      change Matrix.scalar (Fin k) (u : ℂ) * h.val = _
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rw [← hz, hzi, mul_inv_cancel_left]
  have hW (g : G) : b (x * (zi * g)) = (centralCharacter es u⁻¹ : ℂ) * b (x * g) := by
    rw [show zi * g = g * zi from Matrix.GeneralLinearGroup.scalar_commute u⁻¹ g, ← mul_assoc]
    exact model_mul_scalar hLen hb u⁻¹ (x * g)
  rw [← integral_mul_left_eq_self (μ := μ) (squareKernel d (dilateMatrixTest u Φ) (fun g => b (x * g)) s) zi,
    ← integral_const_mul]
  apply integral_congr_ae (ae_of_all _ fun g => ?_)
  rw [squareKernel, hΦ, hW, squareDilationWeight, squareKernel]
  rw [map_mul determinant, map_mul (characterWeight d ((t : ℂ) / 2 + s))]
  change Φ g.val * (_ * _) * _ = _ * characterWeight d _ (determinant zi) * (Φ g.val * _ * _)
  ring

/-- Both spectral ends of a square integral can be evaluated on the same finite combination
of normalized convolution vectors. The square test is a common scalar dilation of a finite
linear combination, and the threshold is independent of the Whittaker evaluation point. -/
def ComplexGapSquareDilationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [κ.IsHaarMeasure] [IsFiniteMeasure κ]
    (a : ℂˣ) (d : ComplexCharacterData) (e : Fin k → ComplexCharacterData),
    let es := List.ofFn e
    ∀ (B : complexStandardKFinite k es →ₗ[ℂ] (G → ℂ)), IsComplexWhittakerIntertwiner t es a B →
    ∀ (f : complexStandardKFinite k es) (l : ℕ) (Φ : 𝓢(Mat, ℂ)) (Φj : Fin l → 𝓢(Mat, ℂ))
      (F : Fin l → ℂ → complexStandardKFinite k es) (c : Fin l → ℂ) (u : ℂˣ),
      (∀ j, HasSquareConvolutionTrace μ d e B (Φj j) f (F j)) →
      (∀ X, Φ X = ∑ j, c j * Φj j ((u : ℂ) • X)) →
      FiniteDimensional ℂ (Submodule.span ℂ (range fun h : K => fun X => Φ (h.val⁻¹.val * X))) →
      let Y (s : ℂ) := squareDilationWeight t d es u s • ∑ j, c j • F j s
      ∃ σ : ℝ, ∀ (s : ℂ), σ < s.re → ∀ x : G,
        (complexPairLFactor [d] es).denominator s *
          (∫ h, squareKernel d Φ (fun g => B f (x * g)) s h ∂μ) = B (Y s) x ∧
        (complexPairLFactor [d.inv] (es.map ComplexCharacterData.inv)).denominator s *
          (∫ h, squareKernel d.inv (splitSquareTransform a Φ) (fun g => B f (x * ι g)) s h ∂μ) =
          pairReflectionFactor [d] es a 1 (1 - s) * B (Y (1 - s)) x

set_option maxHeartbeats 2300000 in
theorem complexGapSquareDilation : ComplexGapSquareDilationStatement t := by
  intro μ hμ κ hκ hκf a d e es B hB f l Φ Φj F c u hF hΦ hFin Y
  let D := (complexPairLFactor [d] es).denominator
  let Dd := (complexPairLFactor [d.inv] (es.map ComplexCharacterData.inv)).denominator
  let J (x h : G) := B f (x * h)
  let Jd (x h : G) := B f (x * ι h)
  have hV : B f ∈ complexWhittakerModel t es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hC (x : G) : Continuous (J x) := (hB.2.1 f).continuous.comp (continuous_const.mul continuous_id)
  have hCd (x : G) : Continuous (Jd x) := (hC x).comp (continuous_inverseTranspose k ℂ)
  obtain ⟨M, N, hM⟩ := hB.2.2.1 f
  let C (x : G) := max M 0 * complexMatrixHeight x ^ N
  have hC₀ (x : G) : 0 ≤ C x := mul_nonneg (le_max_right _ _) (pow_nonneg (complexMatrixHeight_nonneg _) _)
  have hBnd (x h : G) : ‖J x h‖ ≤ C x * complexMatrixHeight h ^ N := by
    refine (hM (x * h)).trans ?_
    dsimp only [C]
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (complexMatrixHeight_nonneg _)
      (complexMatrixHeight_mul_le x h) N) (pow_nonneg (complexMatrixHeight_nonneg _) _) (le_max_right _ _)
  have hBndd (x h : G) : ‖Jd x h‖ ≤ C x * complexMatrixHeight h ^ N := by
    simpa only [Jd, J, complexMatrixHeight_inverseTranspose] using hBnd x (ι h)
  let τ (d' : ComplexCharacterData) := ((k : ℕ) : ℝ) + N - ((t : ℂ) / 2 + d'.exponent).re
  choose bj hbj using fun j => (hF j).2
  obtain ⟨b, hb⟩ := (finite_range bj).bddAbove
  let σ := max (max (τ d) (τ d.inv)) b
  have hO (s : ℂ) (hs : σ < s.re) (x : G) :
      D s * (∫ h, squareKernel d Φ (J x) s h ∂μ) = B (Y s) x := by
    have hKer (g : G) : squareKernel d Φ (J x) s g =
        ∑ j, c j * squareKernel d (dilateMatrixTest u (Φj j)) (J x) s g := by
      unfold squareKernel
      rw [hΦ, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dilateMatrixTest_apply]
      ring
    have hI (j : Fin l) : Integrable (squareKernel d (dilateMatrixTest u (Φj j)) (J x) s) μ :=
      (squareKernel_right t μ d (dilateMatrixTest u (Φj j)) (J x) (hC x) N (hC₀ x) (hBnd x)).1 s
        ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hs))
    simp_rw [hKer]
    rw [integral_finsetSum Finset.univ (fun j _ => (hI j).const_mul _)]
    simp only [Y, map_smul, Pi.smul_apply, smul_eq_mul, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, squareKernel_dilate_integral t μ d List.length_ofFn hV (Φj j) u s x]
    have hS₀ := hbj j s ((hb (mem_range_self j)).trans_lt ((le_max_right _ _).trans_lt hs)) x
    have he : (fun g => complexJacquetMatrixIntegrand d (fun g => B f (x * g)) (Φj j) s g) =
        squareKernel d (Φj j) (J x) s := (funext (squareKernel_eq_matrixIntegrand t d (Φj j) (J x) s)).symm
    rw [he] at hS₀
    change B (F j s) x = D s * (∫ h, squareKernel d (Φj j) (J x) s h ∂μ) at hS₀
    rw [hS₀]
    ring
  refine ⟨σ, fun s hs x => ⟨hO s hs x, ?_⟩⟩
  obtain ⟨_, A, Ad, hA, hAd, _, _, ⟨σx, hR⟩, hEq⟩ :=
    complexGapSquareReflection t μ κ a d es List.length_ofFn Φ hFin B hB f x
  have hYj (j : Fin l) : Differentiable ℂ (fun w => B (F j w) x) := by
    obtain ⟨m, Q, v, hQ⟩ := (hF j).1
    simp_rw [hQ, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Differentiable.fun_sum fun i _ => (Q i).differentiable.mul_const _
  have hY : Differentiable ℂ (fun w => B (Y w) x) := by
    have hW := differentiable_squareDilationWeight t d es u
    dsimp only [Y]
    simp only [map_smul, map_sum, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    exact hW.mul (Differentiable.fun_sum fun j _ => (hYj j).const_mul _)
  have hAP : A = fun w => B (Y w) x := by
    let s₁ : ℂ := ((max σ σx + 1 : ℝ) : ℂ)
    have hs₁ : max σ σx < s₁.re := by simp [s₁]
    apply AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hA.analyticAt w) (fun w _ => hY.analyticAt w) (z₀ := s₁)
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs₁] with w hw
    exact ((hR w ((le_max_right _ _).trans_lt hw)).1).trans (hO w ((le_max_left _ _).trans_lt hw) x)
  have hInt := (squareKernel_right t μ d.inv (splitSquareTransform a Φ) (Jd x)
    (hCd x) N (hC₀ x) (hBndd x)).2
  have hAdEq : EqOn Ad (fun w => Dd w * (∫ h, squareKernel d.inv (splitSquareTransform a Φ) (Jd x) w h ∂μ))
      {w : ℂ | τ d.inv < w.re} := by
    refine eqOn_halfPlane (σ₁ := σx) hAd.differentiableOn
      ((complexPairLFactor [d.inv] _).entire.differentiableOn.mul hInt) ?_
    exact fun w hw => (hR w hw).2
  have hs' : τ d.inv < s.re := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hs)
  have hEq' := hEq (1 - s)
  rw [sub_sub_cancel, hAP] at hEq'
  exact (hAdEq hs').symm.trans hEq'

end Langlands.Global.RankinSelbergGlobal.ComplexGapSquareReflection
