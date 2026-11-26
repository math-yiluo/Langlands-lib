import Langlands.Global.RankinSelberg.ComplexSquareConvolutionUnit
import Langlands.Global.RankinSelberg.ComplexSquareGaussianDerivative
import Langlands.Global.RankinSelberg.ComplexGodementStandardLie
import Langlands.Global.RankinSelberg.ComplexGapLeadingSchwartz

/-! # Differentiating complex square convolution along a matrix exponential -/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open ComplexGodement (characterWeight normPower norm_characterWeight rightExponential
  rightExponential_zero continuous_rightExponential determinantSlope hasDerivAt_weight_rightExponential
  hasDerivAt_rightExponential_val)
open ComplexSquareZeta (squareDirectionalTest squareDirectionalTest_apply)
open ComplexGapLeadingSchwartz (complexGapLeadingSchwartz leadingStack matrixDecay weightedMatrixTail
  exists_integrable_weightedMatrixTail)
open ComplexPlaceAnalytic (two_le_complexMatrixHeight)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}
local notation "n" => (r + 1 : ℕ)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- Left multiplication by a matrix, as a continuous real-linear operator. -/
def squareLeftMultiply (X : Mat) : Mat →L[ℝ] Mat :=
  (mulLeftLinearMap (Fin n) ℝ X).toContinuousLinearMap

@[simp] theorem squareLeftMultiply_apply (X Y : Mat) : squareLeftMultiply X Y = X * Y := rfl

/-- Left group translation transfers to the inverse left translate of the test and a scalar
from its determinant weight. -/
theorem squareConvolution_leftShear (μ : Measure G) [μ.IsMulLeftInvariant]
    (d : ComplexCharacterData) (s : ℂ) (Φ : Mat → ℂ) (b : G → ℂ) (x k : G) :
    (∫ g, complexJacquetMatrixIntegrand d (fun g => b (x * k * g)) Φ s g ∂μ) =
      characterWeight d (s + (r : ℂ) / 2) (determinant k⁻¹) *
        ∫ g, Φ (k⁻¹.val * g.val) * (characterWeight d (s + (r : ℂ) / 2) (determinant g) * b (x * g)) ∂μ := by
  let C := characterWeight d (s + (r : ℂ) / 2)
  let K (g : G) := Φ (k⁻¹.val * g.val) * (C (determinant g) * b (x * g))
  rw [← integral_mul_left_eq_self (μ := μ) K k, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [K, C, complexJacquetMatrixIntegrand, square_detPower_eq_normPower]
  have h₁ : k⁻¹.val * (k * g).val = g.val := by
    rw [← Units.val_mul, inv_mul_cancel_left]
  have h₂ : characterWeight d (s + (r : ℂ) / 2) (determinant k⁻¹) *
      characterWeight d (s + (r : ℂ) / 2) (determinant (k * g)) =
        characterWeight d (s + (r : ℂ) / 2) (determinant g) := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_left]
  rw [h₁, ← mul_assoc x k g]
  calc
    _ = Φ g.val * (characterWeight d (s + (r : ℂ) / 2) (determinant g) * b (x * k * g)) := by
      change _ = Φ g.val * (((d.character (determinant g) : ℂ) *
        normPower (s + (r : ℂ) / 2) (determinant g)) * b (x * k * g))
      ring
    _ = _ := by rw [← h₂]; ring

open scoped Matrix.Norms.Elementwise in
private theorem squareSchwartz_leftBound (Φ : 𝓢(Mat, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : G) (Y : Mat),
      ‖Φ (k.val * Y)‖ ≤ C * complexMatrixHeight k ^ p * matrixDecay p Y := by
  obtain ⟨C, hC, h⟩ := complexGapLeadingSchwartz n 0 (Nat.succ_pos r) Φ p 0
  refine ⟨C, hC, fun k Y => ?_⟩
  have he : leadingStack Y (0 : Matrix (Fin 0) (Fin n) ℂ) = Y := by
    apply Matrix.ext
    intro i j
    exact Fin.append_left (fun i => Y i j) (fun _ => 0) i
  simpa only [he, Nat.add_zero, pow_zero, mul_one, matrixDecay, div_eq_mul_inv] using
    h k Y (0 : Matrix (Fin 0) (Fin n) ℂ)

open scoped Matrix.Norms.Elementwise in
private theorem matrixDecay_nonneg (p : ℕ) (Y : Mat) : 0 ≤ matrixDecay p Y :=
  inv_nonneg.mpr (pow_nonneg (add_nonneg zero_le_one (norm_nonneg Y)) p)

private theorem hasDerivAt_inverse_exponential_mul (X Y : Mat) (t : ℝ) :
    HasDerivAt (fun u => (rightExponential (1 : G) X u)⁻¹.val * Y)
      ((-X) * ((rightExponential (1 : G) X t)⁻¹.val * Y)) t := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) t).mul_const Y
  have hc : (-X) * NormedSpace.exp (t • (-X)) = NormedSpace.exp (t • (-X)) * (-X) :=
    ((Commute.refl (-X)).smul_right t).exp_right.eq
  simpa only [rightExponential, one_mul, matrixExponentialGL_inv, ← smul_neg,
    matrixExponentialGL_coe, ← mul_assoc, hc] using h

private theorem height_bound_shift {b : G → ℂ} {C : ℝ} (hC : 0 ≤ C) {M : ℕ}
    (hb : ∀ g, ‖b g‖ ≤ C * complexMatrixHeight g ^ M) (x : G) (g : G) :
    ‖b (x * g)‖ ≤ (C * complexMatrixHeight x ^ M) * complexMatrixHeight g ^ M := by
  have h₁ (g : G) : 1 ≤ complexMatrixHeight g := one_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) g)
  have hh := max_complexMatrixHeight_mul_le x g
  rw [max_eq_right (h₁ (x * g)), max_eq_right (h₁ x), max_eq_right (h₁ g)] at hh
  calc
    _ ≤ C * complexMatrixHeight (x * g) ^ M := hb _
    _ ≤ C * (complexMatrixHeight x * complexMatrixHeight g) ^ M :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (complexMatrixHeight_nonneg _) hh _) hC
    _ = _ := by rw [mul_pow, mul_assoc]

/-- The translated matrix convolution differentiates through the integral in the half-plane
provided by the moderate height bound. -/
theorem hasDerivAt_squareConvolution_integral (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) {b : G → ℂ} (hbc : Continuous b) {C : ℝ} (hC : 0 ≤ C) {M : ℕ}
    (hb : ∀ g, ‖b g‖ ≤ C * complexMatrixHeight g ^ M)
    (Φ : 𝓢(Mat, ℂ)) (s : ℂ) (hs : (n : ℝ) + M ≤ (d.exponent + s + (r : ℂ) / 2).re)
    (x : G) (X : Mat) :
    let Ψ := squareDirectionalTest (squareLeftMultiply (-X)) Φ
    let weight g := characterWeight d (s + (r : ℂ) / 2) (determinant g) * b (x * g)
    HasDerivAt (fun t => ∫ g, Φ ((rightExponential (1 : G) X t)⁻¹.val * g.val) * weight g ∂μ)
      (∫ g, Ψ g.val * weight g ∂μ) 0 := by
  intro Ψ weight
  let γ (t : ℝ) := (rightExponential (1 : G) X t)⁻¹
  have hc : Continuous γ := (continuous_rightExponential 1 X).inv
  have hγ₀ : γ 0 = 1 := by simp [γ]
  let K (Θ : 𝓢(Mat, ℂ)) (t : ℝ) (g : G) := Θ ((γ t).val * g.val) * weight g
  have hK (Θ : 𝓢(Mat, ℂ)) (t : ℝ) : Continuous (K Θ t) := by
    exact (Θ.continuous.comp (continuous_const.matrix_mul Units.continuous_val)).mul
      (((ComplexGodement.continuous_characterWeight d _).comp continuous_complexDeterminant).mul
        (hbc.comp (continuous_const.mul continuous_id)))
  let L := complexMatrixHeight (1 : G) + 1
  let S : Set ℝ := {t | complexMatrixHeight (γ t) < L}
  have hS : S ∈ 𝓝 0 := (continuous_complexMatrixHeight.comp hc).continuousAt.eventually_lt
    continuousAt_const (by simp [hγ₀, L])
  let u := (d.exponent + s + (r : ℂ) / 2).re
  obtain ⟨p, hp₀⟩ := exists_integrable_weightedMatrixTail r M u hs
  let ν := complexGeneralLinearHaar n
  let e₀ := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n
  let : LocallyCompactSpace G := e₀.locallyCompactSpace
  let : SecondCountableTopology G := e₀.secondCountableTopology
  have hp : Integrable (weightedMatrixTail M p u) μ := by
    have hμ : μ = μ.haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul _ _
    rw [hμ]
    exact hp₀.smul_measure_nnreal
  have hL : 0 ≤ L := add_nonneg (complexMatrixHeight_nonneg (1 : G)) zero_le_one
  have hBound (Θ : 𝓢(Mat, ℂ)) : ∃ D : ℝ, ∀ t ∈ S, ∀ g : G,
      ‖K Θ t g‖ ≤ D * weightedMatrixTail M p u g := by
    obtain ⟨D, hD, hΘ⟩ := squareSchwartz_leftBound (operatorToEntry Θ) p
    refine ⟨D * L ^ p * (C * complexMatrixHeight x ^ M), fun t ht g => ?_⟩
    have hΘ₁ := hΘ (γ t) g.val
    have hΘ₂ : ‖Θ ((γ t).val * g.val)‖ ≤ D * L ^ p * matrixDecay p g.val := by
      apply hΘ₁.trans
      have hg := complexMatrixHeight_nonneg (γ t)
      have ht' : complexMatrixHeight (γ t) ≤ L := (show _ < L from ht).le
      have hdec := matrixDecay_nonneg p g.val
      gcongr
    have hw : ‖characterWeight d (s + (r : ℂ) / 2) (determinant g)‖ =
        complexNormalizedAbs g.val.det ^ u := by
      rw [norm_characterWeight, ← add_assoc]
      rfl
    change ‖Θ ((γ t).val * g.val) *
      (characterWeight d (s + (r : ℂ) / 2) (determinant g) * b (x * g))‖ ≤ _
    rw [norm_mul, norm_mul, hw]
    calc
      _ ≤ (D * L ^ p * matrixDecay p g.val) * (complexNormalizedAbs g.val.det ^ u *
          ((C * complexMatrixHeight x ^ M) * complexMatrixHeight g ^ M)) := by
        have := height_bound_shift hC hb x g
        have hδ : 0 ≤ complexNormalizedAbs g.val.det ^ u :=
          Real.rpow_nonneg (sq_nonneg _) _
        have : 0 ≤ D * L ^ p * matrixDecay p g.val :=
          mul_nonneg (mul_nonneg hD (pow_nonneg hL _)) (matrixDecay_nonneg p g.val)
        gcongr
      _ = _ := by unfold weightedMatrixTail; ring
  obtain ⟨D, hD⟩ := hBound Ψ
  obtain ⟨D₀, hD₀⟩ := hBound Φ
  have hInt : Integrable (K Φ 0) μ :=
    (hp.const_mul D₀).mono' (hK Φ 0).aestronglyMeasurable (ae_of_all _ fun g => hD₀ 0 (mem_of_mem_nhds hS) g)
  have hDiff (t : ℝ) (g : G) : HasDerivAt (fun u => K Φ u g) (K Ψ t g) t := by
    have hh := ((Φ.hasFDerivAt ((γ t).val * g.val)).comp_hasDerivAt t
      (hasDerivAt_inverse_exponential_mul X g.val t)).mul_const (weight g)
    simpa only [K, Function.comp_def, Ψ, squareDirectionalTest_apply, squareLeftMultiply_apply, γ] using hh
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := K Φ) (F' := K Ψ) (s := S)
    (bound := fun g => D * weightedMatrixTail M p u g)
    hS (Eventually.of_forall fun t => (hK Φ t).aestronglyMeasurable)
    hInt (hK Ψ 0).aestronglyMeasurable (ae_of_all _ fun g t ht => hD t ht g)
    (hp.const_mul D) (ae_of_all _ fun g t _ => hDiff t g)).2
  simpa only [K, γ, rightExponential_zero, inv_one, Units.val_one, Matrix.one_mul] using h

/-- The determinant slope along any real Lie direction is entire in the complex power. -/
theorem differentiable_determinantSlope (d : ComplexCharacterData) (X : Mat) :
    Differentiable ℂ (fun s => determinantSlope d s X) := by
  let γ (t : ℝ) := rightExponential (1 : G) X t
  let ℓ (t : ℝ) := Real.log (complexNormalizedAbs (γ t).val.det)
  have hγ₀ : γ 0 = 1 := rightExponential_zero 1 X
  have hℓ₀ : ℓ 0 = 0 := by simp [ℓ, hγ₀, complexNormalizedAbs]
  have hℓ : DifferentiableAt ℝ ℓ 0 := by
    have hdet : Differentiable ℝ (fun Y : Mat => Y.det) :=
      ComplexMaximalParabolicIntegration.contDiff_det.differentiable (by simp)
    have hv := (hdet _).comp 0 (hasDerivAt_rightExponential_val (1 : G) X 0).differentiableAt
    have hne : (γ 0).val.det ≠ 0 := (γ 0).det_ne_zero
    have hN : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖) (γ 0).val.det := contDiffAt_norm ℝ hne
    have hnorm : DifferentiableAt ℝ (fun t => ‖(γ t).val.det‖) 0 :=
      (hN.differentiableAt (by simp)).comp 0 hv
    have hpow : ‖(γ 0).val.det‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
    exact (hnorm.pow 2).log hpow
  have hA := hasDerivAt_weight_rightExponential d 0 (1 : G) X
  simp only [map_one, one_mul] at hA
  have hAffine (s : ℂ) : determinantSlope d s X =
      determinantSlope d 0 X + s * Complex.ofReal (deriv ℓ 0) := by
    have hd := (((hℓ.hasDerivAt).ofReal_comp).const_mul s).cexp
    have h₀ : characterWeight d 0 (determinant (rightExponential (1 : G) X 0)) = 1 := by
      rw [rightExponential_zero, map_one, map_one]
    have h := hA.mul hd
    have he (t : ℝ) : characterWeight d 0 (determinant (γ t)) * Complex.exp (s * (ℓ t : ℂ)) =
        characterWeight d s (determinant (γ t)) := by
      change ((_ : ℂ) * normPower 0 (determinant (γ t))) * _ = (_ : ℂ) * normPower s (determinant (γ t))
      have hnp : normPower 0 (determinant (γ t)) = 1 := Complex.cpow_zero _
      rw [hnp, mul_one, ← square_detPower_eq_normPower]
      rfl
    have h' : HasDerivAt (fun t => characterWeight d s (determinant (γ t)))
        (determinantSlope d 0 X + s * Complex.ofReal (deriv ℓ 0)) 0 := by
      have he' : (fun t => characterWeight d 0 (determinant (γ t)) * Complex.exp (s * (ℓ t : ℂ))) =
          fun t => characterWeight d s (determinant (γ t)) := funext he
      change HasDerivAt (fun t => characterWeight d 0 (determinant (γ t)) * Complex.exp (s * (ℓ t : ℂ))) _ 0 at h
      rw [he'] at h
      simpa only [hℓ₀, h₀, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, one_mul] using h
    have hs' := hasDerivAt_weight_rightExponential d s (1 : G) X
    simp only [map_one, one_mul] at hs'
    exact hs'.unique h'
  rw [funext hAffine]
  exact (differentiable_const _).add (differentiable_id.mul_const _)

/-- A right matrix derivative of square convolution is the convolution with the differentiated
test plus the determinant slope times the original convolution. -/
def ComplexSquareConvolutionDerivativeStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (d : ComplexCharacterData) (b : G → ℂ), Continuous b →
    ∀ (C : ℝ) (M : ℕ), 0 ≤ C → (∀ g, ‖b g‖ ≤ C * complexMatrixHeight g ^ M) →
    ∀ (Φ : 𝓢(Mat, ℂ)) (s : ℂ), (n : ℝ) + M ≤ (d.exponent + s + (r : ℂ) / 2).re →
    ∀ (x : G) (X : Mat),
      let Ψ := squareDirectionalTest (squareLeftMultiply (-X)) Φ
      let K (Θ : 𝓢(Mat, ℂ)) (y : G) := ∫ g,
        complexJacquetMatrixIntegrand d (fun g => b (y * g)) Θ s g ∂μ
      HasDerivAt (fun t => K Φ (rightExponential x X t))
        (determinantSlope d (s + (r : ℂ) / 2) (-X) * K Φ x + K Ψ x) 0

theorem complexSquareConvolutionDerivative : ComplexSquareConvolutionDerivativeStatement (r := r) := by
  intro μ hμ d b hbc C M hC hb Φ s hs x X Ψ K
  let γ (t : ℝ) := rightExponential (1 : G) X t
  let u := s + (r : ℂ) / 2
  let a (t : ℝ) := characterWeight d u (determinant (γ t)⁻¹)
  let v (t : ℝ) := ∫ g, Φ ((γ t)⁻¹.val * g.val) *
    (characterWeight d u (determinant g) * b (x * g)) ∂μ
  have ha : HasDerivAt a (determinantSlope d u (-X)) 0 := by
    have h := hasDerivAt_weight_rightExponential d u (1 : G) (-X)
    simpa only [a, γ, rightExponential, one_mul, map_one, matrixExponentialGL_inv, smul_neg] using h
  have hv : HasDerivAt v (K Ψ x) 0 := by
    have he (Θ : 𝓢(Mat, ℂ)) : (∫ g, Θ g.val *
        (characterWeight d u (determinant g) * b (x * g)) ∂μ) = K Θ x := by
      apply integral_congr_ae (ae_of_all _ fun g => ?_)
      simp only [complexJacquetMatrixIntegrand, square_detPower_eq_normPower, u]
      change _ * (((d.character (determinant g) : ℂ) * normPower _ (determinant g)) * _) = _
      ring
    have h := hasDerivAt_squareConvolution_integral μ d hbc hC hb Φ s hs x X
    change HasDerivAt v (∫ g, Ψ g.val * (characterWeight d u (determinant g) * b (x * g)) ∂μ) 0 at h
    rw [he] at h
    exact h
  have hEq (t : ℝ) : K Φ (rightExponential x X t) = a t * v t := by
    simpa only [K, rightExponential, γ, u, a, v, one_mul] using
      squareConvolution_leftShear μ d s Φ b x (matrixExponentialGL ℂ n (t • X))
  have ha₀ : a 0 = 1 := by simp [a, γ]
  have hv₀ : v 0 = K Φ x := by simpa only [rightExponential_zero, ha₀, one_mul] using (hEq 0).symm
  have hprod := ha.mul hv
  rw [ha₀, hv₀, one_mul] at hprod
  exact hprod.congr_of_eventuallyEq (Eventually.of_forall hEq)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
