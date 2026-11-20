import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.RingTheory.Complex

/-! # Self-dual trace Fourier transformation in finitely many complex coordinates -/

noncomputable section

open MeasureTheory WithLp
open scoped ENNReal FourierTransform NNReal RealInnerProductSpace SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexTraceFourier

open ArchimedeanLocal Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

/-- Finite complex coordinates with the real Euclidean inner product. -/
abbrev Coordinates (ι : Type*) := PiLp 2 (fun _ : ι => ℂ)

/-- Forget the Euclidean norm in favor of the ordinary finite product norm. -/
abbrev coordinates : Coordinates ι ≃L[ℝ] (ι → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℂ)

theorem coordinates_measurePreserving : MeasurePreserving (coordinates (ι := ι)) := by
  let b := Complex.orthonormalBasisOneI
  let B := Pi.orthonormalBasis (fun _ : ι => b)
  let e := coordinates (ι := ι)
  refine ⟨e.continuous.measurable, ?_⟩
  change (volume : Measure (Coordinates ι)).map e = volume
  rw [← B.addHaar_eq_volume, Module.Basis.map_addHaar, Module.Basis.addHaar_eq_iff]
  have h : parallelepiped (B.toBasis.map e.toLinearEquiv) =
      Set.pi Set.univ (fun _ : ι => parallelepiped b) := by
    ext x
    simp only [parallelepiped_basis_eq, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      ← b.coe_toBasis, Module.Basis.map_repr, OrthonormalBasis.coe_toBasis_repr_apply]
    change (∀ ij : (Σ _ : ι, Fin 2), b.repr (x ij.1) ij.2 ∈ Set.Icc 0 1) ↔
      ∀ i j, b.repr (x i) j ∈ Set.Icc 0 1
    exact Sigma.forall
  change volume (parallelepiped (B.toBasis.map e.toLinearEquiv)) = 1
  rw [h, volume_pi_pi]
  simp [b.volume_parallelepiped]

/-- Density of the self-dual measure on a single complex coordinate relative to area. -/
def scale (a : ℂˣ) : ℝ≥0 := 2 * ‖(a : ℂ)‖₊

theorem scale_pos (a : ℂˣ) : 0 < scale a := by
  exact mul_pos (by norm_num) (nnnorm_pos.mpr a.ne_zero)

theorem measure_eq (a : ℂˣ) :
    (complexSelfDualMeasure a).measure = scale a • (volume : Measure ℂ) := by
  rw [complexSelfDualMeasure, complexScaledMeasure_measure, scale, mul_comm]

theorem product_measure_eq (a : ℂˣ) :
    Measure.pi (fun _ : ι => (complexSelfDualMeasure a).measure) =
      scale a ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  simp only [measure_eq, Langlands.HarmonicAnalysis.pi_nnreal_smul,
    Finset.prod_const, Finset.card_univ]
  rfl

/-- The real frequency giving the negative complex trace pairing in one coordinate. -/
private def scalarFrequency (a : ℂˣ) : ℂ ≃L[ℝ] ℂ :=
  let e := LinearEquiv.smulOfNeZero ℂ ℂ (2 * (a : ℂ)) (mul_ne_zero (by norm_num) a.ne_zero)
  (e.restrictScalars ℝ).toContinuousLinearEquiv.trans Complex.conjCLE

/-- Apply the trace frequency change to every complex coordinate. -/
def frequency (a : ℂˣ) : Coordinates ι ≃L[ℝ] Coordinates ι :=
  let e := LinearEquiv.piCongrRight (fun _ : ι => (scalarFrequency a).toLinearEquiv)
  coordinates.trans (e.toContinuousLinearEquiv.trans coordinates.symm)

@[simp] theorem frequency_apply (a : ℂˣ) (y : Coordinates ι) (i : ι) :
    frequency a y i = starRingEnd ℂ (2 * (a : ℂ) * y i) := rfl

private theorem inner_frequency (a : ℂˣ) (x y : Coordinates ι) :
    inner ℝ x (frequency a y) = Algebra.trace ℝ ℂ ((a : ℂ) * ∑ i, x i * y i) := by
  have h (i : ι) : inner ℝ (x i) (frequency a y i) = 2 * ((a : ℂ) * (x i * y i)).re := by
    rw [Complex.inner, frequency_apply, ← map_mul, Complex.conj_re,
      show 2 * (a : ℂ) * y i * x i = 2 * ((a : ℂ) * (x i * y i)) by ring]
    simp [Complex.mul_re]
  simp only [PiLp.inner_apply, h, ← Finset.mul_sum, ← Complex.re_sum, Algebra.trace_complex_apply]

private def phaseValue (a : ℂˣ) : ℂ := (2 * (a : ℂ)) / (scale a : ℝ)

private theorem norm_phaseValue (a : ℂˣ) : ‖phaseValue a‖ = 1 := by
  rw [phaseValue, norm_div, norm_mul, Complex.norm_two, Complex.norm_real,
    Real.norm_of_nonneg (scale a).coe_nonneg]
  exact div_self (NNReal.coe_ne_zero.mpr (scale_pos a).ne')

private def phaseIsometry (a : ℂˣ) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv := ((LinearEquiv.smulOfNeZero ℂ ℂ (phaseValue a)
    (norm_ne_zero_iff.mp (norm_phaseValue a ▸ one_ne_zero))).restrictScalars ℝ).trans
      Complex.conjLIE.toLinearEquiv
  norm_map' z := by
    change ‖starRingEnd ℂ (phaseValue a * z)‖ = ‖z‖
    rw [Complex.norm_conj, norm_mul, norm_phaseValue, one_mul]

private theorem frequency_eq_smul (a : ℂˣ) (y : Coordinates ι) :
    frequency a y = (scale a : ℝ) • LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => phaseIsometry a) y := by
  ext i
  change Complex.conjLIE (2 * (a : ℂ) * y i) =
    (scale a : ℝ) • Complex.conjLIE (phaseValue a * y i)
  rw [← map_smul]
  congr 1
  rw [Complex.real_smul, phaseValue]
  field_simp [Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (scale_pos a).ne')]

private theorem finrank_coordinates : Module.finrank ℝ (Coordinates ι) = 2 * Fintype.card ι := by
  rw [coordinates.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype ℝ]
  simp [Complex.finrank_real_complex, mul_comm]

/-- The real volume Jacobian of the frequency change is the square of the product of the
one-coordinate self-dual densities. -/
theorem integral_frequency (a : ℂˣ) (f : Coordinates ι → ℂ) :
    (∫ y, f (frequency a y)) = ((scale a : ℝ) ^ (2 * Fintype.card ι))⁻¹ • ∫ y, f y := by
  simp_rw [frequency_eq_smul]
  let e := LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => phaseIsometry a)
  calc
    (∫ y, f ((scale a : ℝ) • e y)) = ∫ y, f ((scale a : ℝ) • y) :=
      e.measurePreserving.integral_comp' (f := e.toMeasurableEquiv)
        (fun y => f ((scale a : ℝ) • y))
    _ = _ := by
      rw [Measure.integral_comp_smul_of_nonneg volume f (scale a : ℝ)
        (hR := (scale a).coe_nonneg), finrank_coordinates]

/-- Jacquet's negative trace Fourier transform with the self-dual product measure. -/
def transform (a : ℂˣ) (Φ : 𝓢(ι → ℂ, ℂ)) : 𝓢(ι → ℂ, ℂ) :=
  ((scale a : ℝ) ^ Fintype.card ι) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (coordinates.symm.trans (frequency a))
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinates Φ))

/-- The finite-coordinate transform evaluates using the self-dual product measure and the
negative sum of coordinate products in the complex additive character. -/
def ComplexTraceFourierEvaluationStatement : Prop :=
  ∀ (a : ℂˣ) (Φ : 𝓢(ι → ℂ, ℂ)) (x : ι → ℂ),
    transform a Φ x = ∫ y : ι → ℂ, Φ y *
      (complexScaledCharacter a).complex (-∑ i, y i * x i)
      ∂Measure.pi (fun _ : ι => (complexSelfDualMeasure a).measure)

theorem transform_apply : ComplexTraceFourierEvaluationStatement (ι := ι) := by
  intro a Φ x
  rw [product_measure_eq, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_pow]
  simp only [transform, smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, ContinuousLinearEquiv.trans_apply, SchwartzMap.fourier_coe, Real.fourier_eq]
  congr 1
  let K (y : Coordinates ι) : ℂ :=
    Real.fourierChar (-inner ℝ y (frequency a (coordinates.symm x))) • Φ (coordinates y)
  calc
    (∫ y, K y) = ∫ y : ι → ℂ, K (coordinates.symm y) :=
      ((coordinates_measurePreserving (ι := ι)).symm
        (MeasurableEquiv.toLp 2 (ι → ℂ)).symm |>.integral_comp'
        (f := MeasurableEquiv.toLp 2 (ι → ℂ)) K).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [K, inner_frequency, ContinuousLinearEquiv.apply_symm_apply,
        HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply,
        Circle.smul_def, smul_eq_mul, mul_neg, map_neg]
      exact mul_comm _ _

end Langlands.Global.RankinSelbergGlobal.ComplexTraceFourier
