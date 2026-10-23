import Langlands.Global.AdelicGL
import Langlands.Global.ArchimedeanEnvelopingAction
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Compact smooth archimedean kernels and raw right convolution -/

noncomputable section
universe u
open MeasureTheory
open scoped Classical

namespace Langlands.Global.ArchimedeanGL
variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The original completion topology on the group is Hausdorff. -/
instance infiniteAdelicGL_t2Space : T2Space (InfiniteAdelicGL K n) := by
  let : T2Space (NumberField.InfiniteAdeleRing K) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace K) → v.Completion))
  infer_instance

/-- Local compactness for the original finite matrix topology and units topology. -/
instance infiniteAdelicGL_locallyCompactSpace : LocallyCompactSpace (InfiniteAdelicGL K n) := by
  let : T2Space (NumberField.InfiniteAdeleRing K) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace K) → v.Completion))
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) (NumberField.InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → NumberField.InfiniteAdeleRing K))
  infer_instance

/-- Compactly supported members of the actual smooth-function space. -/
def compactlySupportedSmoothFunctions : Submodule ℂ (SmoothFunctions K n) where
  carrier := {f | HasCompactSupport f.val}
  zero_mem' := HasCompactSupport.zero
  add_mem' hf hg := hf.add hg
  smul_mem' _ _ hf := hf.smul_left

abbrev SmoothCompactKernel := ↥(compactlySupportedSmoothFunctions K n)

/-- The Borel sigma algebra of the published topology, available for local installation. -/
@[instance_reducible]
def borelMeasurableSpace : MeasurableSpace (InfiniteAdelicGL K n) :=
  borel (InfiniteAdelicGL K n)

omit [NumberField K] in
/-- Compatibility is with exactly the existing topology. -/
theorem borelMeasurableSpace_borelSpace :
    @BorelSpace (InfiniteAdelicGL K n) _ (borelMeasurableSpace K n) := by
  let := borelMeasurableSpace K n
  exact ⟨rfl⟩

/-- The kernel inclusion into continuous complex functions. -/
def kernelToContinuousMap : SmoothCompactKernel K n →ₗ[ℂ] C(InfiniteAdelicGL K n, ℂ) :=
  (toContinuousMap K n).comp (compactlySupportedSmoothFunctions K n).subtype

@[simp]
theorem kernelToContinuousMap_apply (κ : SmoothCompactKernel K n) (g : InfiniteAdelicGL K n) :
    kernelToContinuousMap K n κ g = κ.val.val g := rfl

theorem smoothCompactKernel_hasCompactSupport (κ : SmoothCompactKernel K n) :
    HasCompactSupport κ.val.val := κ.property

/-- At rank zero the group is a singleton, so every smooth function has compact support. -/
theorem hasCompactSupport_rankZero (f : SmoothFunctions K 0) : HasCompactSupport f.val := by
  let : Subsingleton (InfiniteAdelicGL K 0) := ⟨by
    intro g h
    apply Units.ext
    ext i
    exact Fin.elim0 i⟩
  exact HasCompactSupport.of_compactSpace f.val

section Measure
variable [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]

/-- A chosen left Haar measure for any Borel measurable structure on the original topology. -/
def leftHaarMeasure : Measure (InfiniteAdelicGL K n) := Measure.haar

instance leftHaarMeasure_isHaarMeasure : (leftHaarMeasure K n).IsHaarMeasure := by
  unfold leftHaarMeasure
  infer_instance

theorem leftHaarMeasure_ne_zero : leftHaarMeasure K n ≠ 0 := NeZero.ne _

/-- Haar existence is intrinsic, with no measure-existence assumption. -/
theorem exists_leftHaarMeasure :
    ∃ μ : Measure (InfiniteAdelicGL K n), μ.IsHaarMeasure ∧ μ ≠ 0 :=
  ⟨leftHaarMeasure K n, inferInstance, leftHaarMeasure_ne_zero K n⟩

variable (μ : Measure (InfiniteAdelicGL K n))

/-- Raw right convolution; when μ is left Haar this is the left-Haar convention. -/
def rawConvolution (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n)
    (g : InfiniteAdelicGL K n) : ℂ :=
  ∫ y, f y * κ.val.val (y⁻¹ * g) ∂μ

omit [BorelSpace (InfiniteAdelicGL K n)] in
@[simp]
theorem rawConvolution_apply (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n)
    (g : InfiniteAdelicGL K n) :
    rawConvolution K n μ f κ g = ∫ y, f y * κ.val.val (y⁻¹ * g) ∂μ := rfl

variable [IsFiniteMeasureOnCompacts μ]

/-- Pointwise integrability needs compact finiteness, not invariance. -/
theorem convolution_integrable (f : C(InfiniteAdelicGL K n, ℂ))
    (κ : SmoothCompactKernel K n) (g : InfiniteAdelicGL K n) :
    Integrable (fun y => f y * κ.val.val (y⁻¹ * g)) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact f.continuous.mul ((continuous K n κ.val).comp
      (continuous_inv.mul continuous_const))
  · have h := κ.property.comp_homeomorph
      ((Homeomorph.inv (InfiniteAdelicGL K n)).trans (Homeomorph.mulRight g))
    exact h.mul_left

theorem rawConvolution_add_left (f h : C(InfiniteAdelicGL K n, ℂ))
    (κ : SmoothCompactKernel K n) :
    rawConvolution K n μ (f + h) κ = rawConvolution K n μ f κ + rawConvolution K n μ h κ := by
  funext g
  simp only [rawConvolution, ContinuousMap.add_apply, add_mul, Pi.add_apply]
  exact integral_add (convolution_integrable K n μ f κ g) (convolution_integrable K n μ h κ g)

omit [BorelSpace (InfiniteAdelicGL K n)] [IsFiniteMeasureOnCompacts μ] in
theorem rawConvolution_smul_left (c : ℂ) (f : C(InfiniteAdelicGL K n, ℂ))
    (κ : SmoothCompactKernel K n) :
    rawConvolution K n μ (c • f) κ = c • rawConvolution K n μ f κ := by
  funext g
  simp only [rawConvolution, ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul, Pi.smul_apply]

theorem rawConvolution_add_right (f : C(InfiniteAdelicGL K n, ℂ))
    (κ η : SmoothCompactKernel K n) :
    rawConvolution K n μ f (κ + η) = rawConvolution K n μ f κ + rawConvolution K n μ f η := by
  funext g
  change (∫ y, f y * (κ.val.val (y⁻¹ * g) + η.val.val (y⁻¹ * g)) ∂μ) = _
  simp only [mul_add, Pi.add_apply]
  exact integral_add (convolution_integrable K n μ f κ g) (convolution_integrable K n μ f η g)

omit [BorelSpace (InfiniteAdelicGL K n)] [IsFiniteMeasureOnCompacts μ] in
theorem rawConvolution_smul_right (c : ℂ) (f : C(InfiniteAdelicGL K n, ℂ))
    (κ : SmoothCompactKernel K n) :
    rawConvolution K n μ f (c • κ) = c • rawConvolution K n μ f κ := by
  funext g
  change (∫ y, f y * (c * κ.val.val (y⁻¹ * g)) ∂μ) = c * _
  simp only [mul_left_comm (f _) c, integral_const_mul]
  rfl

/-- Complex bilinearity into functions; smoothness of the output is a later obligation. -/
def rawConvolutionLinear :
    C(InfiniteAdelicGL K n, ℂ) →ₗ[ℂ] SmoothCompactKernel K n →ₗ[ℂ] (InfiniteAdelicGL K n → ℂ) where
  toFun f :=
    { toFun := rawConvolution K n μ f
      map_add' := rawConvolution_add_right K n μ f
      map_smul' c κ := rawConvolution_smul_right K n μ c f κ }
  map_add' f h := by
    ext κ g
    exact congrFun (rawConvolution_add_left K n μ f h κ) g
  map_smul' c f := by
    ext κ g
    exact congrFun (rawConvolution_smul_left K n μ c f κ) g

@[simp]
theorem rawConvolutionLinear_apply (f : C(InfiniteAdelicGL K n, ℂ))
    (κ : SmoothCompactKernel K n) (g : InfiniteAdelicGL K n) :
    rawConvolutionLinear K n μ f κ g = ∫ y, f y * κ.val.val (y⁻¹ * g) ∂μ := rfl

end Measure

/-- Existence with the explicitly constructed Borel structure and no measurable-space assumption. -/
theorem exists_borelLeftHaarMeasure :
    letI := borelMeasurableSpace K n
    ∃ μ : Measure (InfiniteAdelicGL K n), μ.IsHaarMeasure ∧ μ ≠ 0 := by
  let := borelMeasurableSpace K n
  let := borelMeasurableSpace_borelSpace K n
  exact exists_leftHaarMeasure K n

end Langlands.Global.ArchimedeanGL
