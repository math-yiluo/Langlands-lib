import Langlands.Representation.Archimedean.OrthogonalGroupAveraging
import Langlands.Representation.Archimedean.RealKTypeCount
import Mathlib.MeasureTheory.Group.Integral

/-! # Left convolution and the orthogonal polynomial degree filtration -/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.OrthogonalFinitePolynomial

open RealKTypeCount

local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ

variable {n : ℕ}

private local instance : SecondCountableTopology (O n) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  exact TopologicalSpace.Subtype.secondCountableTopology
    (Matrix.unitaryGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ))

/-- The degree filtration regarded as finite-dimensional closed subspaces of continuous
functions with the supremum norm. -/
def continuousDegree (n N : ℕ) : Submodule ℂ C(O n, ℂ) :=
  (degreeLE n N).comap (ContinuousMap.coeFnLinearMap ℂ)

theorem mem_continuousDegree {N : ℕ} {f : C(O n, ℂ)} :
    f ∈ continuousDegree n N ↔ (f : O n → ℂ) ∈ degreeLE n N := Iff.rfl

instance (N : ℕ) : FiniteDimensional ℂ (continuousDegree n N) := by
  let L : continuousDegree n N →ₗ[ℂ] degreeLE n N :=
    ((ContinuousMap.coeFnLinearMap ℂ).comp (continuousDegree n N).subtype).codRestrict
      (degreeLE n N) (fun x => mem_continuousDegree.mp x.prop)
  apply Module.Finite.of_injective L
  intro f g h
  apply Subtype.ext
  apply ContinuousMap.coe_injective
  exact congrArg Subtype.val h

private def leftTranslation (k : O n) : C(O n, ℂ) →L[ℂ] C(O n, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ ⟨fun x => k⁻¹ * x, continuous_const.mul continuous_id⟩

private theorem continuous_leftTranslation :
    Continuous (fun p : O n × C(O n, ℂ) => leftTranslation p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (O n × C(O n, ℂ)) × O n => p.1.2 (p.1.1⁻¹ * p.2))
  have heval : Continuous (fun p : C(O n, ℂ) × O n => p.1 p.2) := continuous_eval
  exact heval.comp ((continuous_snd.comp continuous_fst).prodMk
    (((continuous_fst.comp continuous_fst).inv).mul continuous_snd))

section Measure

variable [MeasurableSpace (O n)] [BorelSpace (O n)]
  (μ : Measure (O n)) [IsFiniteMeasure μ]

/-- Left convolution on continuous functions in the supremum norm. -/
def leftConvolution (w : C(O n, ℂ)) : C(O n, ℂ) →L[ℂ] C(O n, ℂ) :=
  compactAverage μ (continuous_leftTranslation (n := n)) w

set_option backward.isDefEq.respectTransparency true in
theorem leftConvolution_apply (w f : C(O n, ℂ)) (x : O n) :
    leftConvolution μ w f x = ∫ k, w k * f (k⁻¹ * x) ∂μ := by
  have hArg : Continuous (fun k : O n => (k, f)) := continuous_id.prodMk continuous_const
  have hTranslate := (continuous_leftTranslation (n := n)).comp hArg
  have hC : Continuous (fun k : O n => w k • leftTranslation k f) :=
    w.continuous.smul hTranslate
  have hI : Integrable (fun k : O n => w k • leftTranslation k f) μ :=
    hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := ((ContinuousMap.evalCLM ℂ (M := ℂ) x).integral_comp_comm hI).symm
  change (ContinuousMap.evalCLM ℂ (M := ℂ) x) (∫ k, w k • leftTranslation k f ∂μ) = _
  rw [h]
  rfl

/-- Left convolution commutes with each right translation. -/
theorem leftConvolution_rightTranslate (w f : C(O n, ℂ)) (g x : O n) :
    leftConvolution μ w ⟨fun y => f (y * g),
      f.continuous.comp (continuous_id.mul continuous_const)⟩ x =
      leftConvolution μ w f (x * g) := by
  simp only [leftConvolution_apply, ContinuousMap.coe_mk, mul_assoc]

variable [IsProbabilityMeasure μ]

/-- Left convolution preserves each polynomial degree subspace of the input. -/
theorem leftConvolution_mem_inputDegree {N : ℕ} (w : C(O n, ℂ)) {f : C(O n, ℂ)}
    (hf : f ∈ continuousDegree n N) : leftConvolution μ w f ∈ continuousDegree n N := by
  exact compactAverage_mem μ continuous_leftTranslation w
    (continuousDegree n N).closed_of_finiteDimensional fun k =>
      mem_continuousDegree.mpr (left_mem_degreeLE (mem_continuousDegree.mp hf) k⁻¹)

variable [μ.IsMulLeftInvariant] [μ.IsInvInvariant]

omit [IsProbabilityMeasure μ] in
/-- The alternate integral in which the kernel is right-translated. -/
theorem leftConvolution_apply_kernel (w f : C(O n, ℂ)) (x : O n) :
    leftConvolution μ w f x = ∫ y, f y * w (x * y⁻¹) ∂μ := by
  rw [leftConvolution_apply]
  calc
    _ = ∫ y, w (x * y) * f ((x * y)⁻¹ * x) ∂μ :=
      (integral_mul_left_eq_self (fun k => w k * f (k⁻¹ * x)) x).symm
    _ = ∫ y, w (x * y⁻¹) * f ((x * y⁻¹)⁻¹ * x) ∂μ :=
      (integral_inv_eq_self _ μ).symm
    _ = _ := by simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right, mul_comm]

/-- A polynomial kernel bounds the degree of every output, for arbitrary continuous input. -/
theorem leftConvolution_mem_kernelDegree {N : ℕ} {w : C(O n, ℂ)} (hw : w ∈ continuousDegree n N)
    (f : C(O n, ℂ)) : leftConvolution μ w f ∈ continuousDegree n N := by
  let W := continuousDegree n N
  let a (y : O n) : C(O n, ℂ) :=
    ⟨fun x => w (x * y⁻¹), w.continuous.comp (continuous_id.mul continuous_const)⟩
  have ha : Continuous a := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact w.continuous.comp (continuous_snd.mul continuous_fst.inv)
  let b (y : O n) := f y • a y
  have hb := (f.continuous.smul ha).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _) (f := b)
  have hz : leftConvolution μ w f = ∫ y, b y ∂μ := by
    apply ContinuousMap.ext
    intro x
    rw [leftConvolution_apply_kernel]
    change _ = (ContinuousMap.evalCLM ℂ (M := ℂ) x) (∫ y, b y ∂μ)
    rw [← (ContinuousMap.evalCLM ℂ (M := ℂ) x).integral_comp_comm hb]
    rfl
  rw [hz]
  exact (W.restrictScalars ℝ).convex.integral_mem W.closed_of_finiteDimensional
    (Filter.Eventually.of_forall fun y => W.smul_mem (f y)
      (mem_continuousDegree.mpr (right_mem_degreeLE (mem_continuousDegree.mp hw) y⁻¹))) hb

end Measure

/-- Left convolution preserves the degree of the input and bounds the degree of the output
by the degree of the kernel. -/
def OrthogonalConvolutionDegreeStatement : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (O n)] [BorelSpace (O n)]
    (μ : Measure (O n)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (N : ℕ) (w f : C(O n, ℂ)),
    (f ∈ continuousDegree n N → leftConvolution μ w f ∈ continuousDegree n N) ∧
    (w ∈ continuousDegree n N → leftConvolution μ w f ∈ continuousDegree n N)

theorem orthogonalConvolutionDegree : OrthogonalConvolutionDegreeStatement :=
  fun _ _ _ μ _ _ _ _ w f => ⟨leftConvolution_mem_inputDegree μ w,
    fun hw => leftConvolution_mem_kernelDegree μ hw f⟩

end Langlands.Archimedean.OrthogonalFinitePolynomial
