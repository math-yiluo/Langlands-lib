import Langlands.Global.ArchimedeanConvolutionRealDifferentiationStatement
import Langlands.Global.ArchimedeanEnvelopingSupportProof
import Langlands.Analysis.CompactLinearParameterIntegralProof
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Smooth compact convolution and transfer of real generators -/

noncomputable section
universe u
open Set Topology MeasureTheory
open scoped Classical Manifold ContDiff Matrix.Norms.Operator Pointwise
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

namespace CompactConvolution

/-- A single compact integration set works on a neighborhood of each output point. -/
theorem exists_compact_support (κ : SmoothCompactKernel K n) (g : InfiniteAdelicGL K n) :
    ∃ k : Set (InfiniteAdelicGL K n), IsCompact k ∧
      ∀ᶠ x in 𝓝 g, ∀ y, y ∉ k → y⁻¹ * x ∉ tsupport κ.val.val := by
  obtain ⟨L, hLc, hLg⟩ := exists_compact_mem_nhds g
  refine ⟨L * (tsupport κ.val.val)⁻¹, hLc.mul κ.property.inv, ?_⟩
  filter_upwards [hLg] with x hx y hy hys
  apply hy
  have hm := mul_mem_mul hx (show (y⁻¹ * x)⁻¹ ∈ (tsupport κ.val.val)⁻¹ from hys)
  simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hm

/-- Left multiplication by the inverse integration variable in real matrix coordinates. -/
def leftLinear (y : InfiniteAdelicGL K n) :
    ArchimedeanMatrix K n →L[ℝ] ArchimedeanMatrix K n :=
  ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)
    (archimedeanGLCoordinates K n y⁻¹ : ArchimedeanMatrix K n)

theorem continuous_leftLinear : Continuous (leftLinear K n) :=
  (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).continuous.comp
    (Units.continuous_val.comp ((archimedeanGLCoordinates K n).continuous.comp continuous_inv))

@[simp]
theorem leftLinear_apply (y : InfiniteAdelicGL K n) (x : ArchimedeanMatrix K n) :
    leftLinear K n y x =
      (archimedeanGLCoordinates K n y⁻¹ : ArchimedeanMatrix K n) * x := rfl

theorem leftLinear_mem_range (y : InfiniteAdelicGL K n)
    {x : ArchimedeanMatrix K n}
    (hx : x ∈ range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) :
    leftLinear K n y x ∈
      range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n) := by
  obtain ⟨h, rfl⟩ := hx
  exact ⟨archimedeanGLCoordinates K n y⁻¹ * h, rfl⟩

section Measure
variable [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
  (μ : Measure (InfiniteAdelicGL K n)) [IsFiniteMeasureOnCompacts μ]

/-- A fixed compact integral, extended to the real matrix parameter space. -/
def extension (k : Set (InfiniteAdelicGL K n))
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n)
    (x : ArchimedeanMatrix K n) : ℂ :=
  ∫ y in k, f y * coordinateExtension K n κ.val (leftLinear K n y x) ∂μ

omit [BorelSpace (InfiniteAdelicGL K n)] [IsFiniteMeasureOnCompacts μ] in
theorem extension_apply (k : Set (InfiniteAdelicGL K n))
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n)
    (g : InfiniteAdelicGL K n) :
    extension K n μ k f κ (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) =
      ∫ y in k, f y * κ.val.val (y⁻¹ * g) ∂μ := by
  unfold extension
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [leftLinear_apply]
  change f y * coordinateExtension K n κ.val
    (archimedeanGLCoordinates K n y⁻¹ * archimedeanGLCoordinates K n g :
      ArchimedeanGL K n) = _
  rw [coordinateExtension_apply, ← map_mul, ContinuousMulEquiv.symm_apply_apply]

theorem extension_contDiffOn (k : Set (InfiniteAdelicGL K n)) (hk : IsCompact k)
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n) :
    ContDiffOn ℝ ∞ (extension K n μ k f κ)
      (range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) := by
  exact (Analysis.compactLinearParameterIntegral
    (InfiniteAdelicGL K n) (ArchimedeanMatrix K n) (ArchimedeanMatrix K n) μ
    k hk _ Units.isOpenEmbedding_val.isOpen_range _
    Units.isOpenEmbedding_val.isOpen_range f f.continuous
    (leftLinear K n) (continuous_leftLinear K n)
    (coordinateExtension K n κ.val) (coordinateExtension_contDiffOn K n κ.val)
    (fun y _ _ hx => leftLinear_mem_range K n y hx)).1

theorem extension_hasFDerivAt (k : Set (InfiniteAdelicGL K n)) (hk : IsCompact k)
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n)
    (g : InfiniteAdelicGL K n) :
    HasFDerivAt (extension K n μ k f κ)
      (∫ y in k, (f y) •
        ((fderiv ℝ (coordinateExtension K n κ.val)
          (leftLinear K n y (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n))).comp
          (leftLinear K n y)) ∂μ)
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) := by
  exact (Analysis.compactLinearParameterIntegral
    (InfiniteAdelicGL K n) (ArchimedeanMatrix K n) (ArchimedeanMatrix K n) μ
    k hk _ Units.isOpenEmbedding_val.isOpen_range _
    Units.isOpenEmbedding_val.isOpen_range f f.continuous
    (leftLinear K n) (continuous_leftLinear K n)
    (coordinateExtension K n κ.val) (coordinateExtension_contDiffOn K n κ.val)
    (fun y _ _ hx => leftLinear_mem_range K n y hx)).2 _ ⟨_, rfl⟩

theorem derivative_integrable (k : Set (InfiniteAdelicGL K n)) (hk : IsCompact k)
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n)
    (g : InfiniteAdelicGL K n) :
    Integrable (fun y => (f y) •
      ((fderiv ℝ (coordinateExtension K n κ.val)
        (leftLinear K n y (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n))).comp
        (leftLinear K n y))) (μ.restrict k) := by
  have hc := Analysis.CompactLinearParameterIntegral.continuousOn_partialDeriv
    (k := k)
    (s := range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n))
    Units.isOpenEmbedding_val.isOpen_range f.continuous (continuous_leftLinear K n)
    (continuous_const (y := (0 : ArchimedeanMatrix K n)))
    (coordinateExtension_contDiffOn K n κ.val)
    (fun y _ x hx => by simpa only [add_zero] using leftLinear_mem_range K n y hx)
  have hc' := hc.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun y (hy : y ∈ k) => ⟨hy, show
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) ∈
        range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n) from ⟨_, rfl⟩⟩)
  simpa only [Function.comp_def, add_zero, id_eq] using! hc'.integrableOn_compact (μ := μ) hk

omit [BorelSpace (InfiniteAdelicGL K n)] [IsFiniteMeasureOnCompacts μ] in
/-- On a neighborhood, the compact integral is the original full integral. -/
theorem extension_eq_raw (k : Set (InfiniteAdelicGL K n))
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n)
    (g : InfiniteAdelicGL K n)
    (hg : ∀ y, y ∉ k → y⁻¹ * g ∉ tsupport κ.val.val) :
    extension K n μ k f κ (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) =
      rawConvolution K n μ f κ g := by
  rw [extension_apply, rawConvolution_apply]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport (hg y hy), mul_zero]

theorem raw_mem_smoothFunctions
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n) :
    rawConvolution K n μ f κ ∈ smoothFunctions K n := by
  intro g
  obtain ⟨k, hk, hlocal⟩ := exists_compact_support K n κ
    ((archimedeanGLCoordinates K n).symm g)
  have hc := (extension_contDiffOn K n μ k hk f κ).contDiffAt
    (Units.isOpenEmbedding_val.isOpen_range.mem_nhds (show
      (g : ArchimedeanMatrix K n) ∈
        range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n) from ⟨g, rfl⟩))
  apply (hc.comp_contMDiffAt
    (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) g)).congr_of_eventuallyEq
  filter_upwards [((archimedeanGLCoordinates K n).symm.continuous.tendsto g).eventually
    hlocal] with h hh
  simpa only [Function.comp_def, ContinuousMulEquiv.apply_symm_apply] using
    (extension_eq_raw K n μ k f κ ((archimedeanGLCoordinates K n).symm h) hh).symm

end Measure

theorem coordinateExtension_eventuallyEq (F : SmoothFunctions K n)
    (H : ArchimedeanMatrix K n → ℂ) (g : InfiniteAdelicGL K n)
    (h : ∀ᶠ x in 𝓝 g,
      F.val x = H (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)) :
    coordinateExtension K n F =ᶠ[
      𝓝 (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)] H := by
  rw [← Units.isOpenEmbedding_val.map_nhds_eq (archimedeanGLCoordinates K n g)]
  change ∀ᶠ (a : ArchimedeanGL K n) in 𝓝 (archimedeanGLCoordinates K n g),
    coordinateExtension K n F (a : ArchimedeanMatrix K n) = H (a : ArchimedeanMatrix K n)
  have ht := (archimedeanGLCoordinates K n).symm.continuous.tendsto
    (archimedeanGLCoordinates K n g)
  change Filter.Tendsto
    (fun a : ArchimedeanGL K n => (archimedeanGLCoordinates K n).symm a)
    (𝓝 (archimedeanGLCoordinates K n g))
    (𝓝 ((archimedeanGLCoordinates K n).symm (archimedeanGLCoordinates K n g))) at ht
  rw [ContinuousMulEquiv.symm_apply_apply] at ht
  filter_upwards [ht.eventually h] with a ha
  simpa only [coordinateExtension_apply, ContinuousMulEquiv.apply_symm_apply] using ha

end CompactConvolution

/-- The actual raw convolution is smooth, and each real generator differentiates its kernel. -/
theorem compactKernelConvolutionRealDifferentiation :
    CompactKernelConvolutionRealDifferentiationStatement K n := by
  intro _ _ μ _ f κ
  let F : SmoothFunctions K n :=
    ⟨rawConvolution K n μ f κ, CompactConvolution.raw_mem_smoothFunctions K n μ f κ⟩
  refine ⟨F, rfl, ?_⟩
  intro X g
  obtain ⟨k, hk, hlocal⟩ := CompactConvolution.exists_compact_support K n κ g
  have heq : coordinateExtension K n F =ᶠ[
      𝓝 (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)]
      CompactConvolution.extension K n μ k f κ := by
    apply CompactConvolution.coordinateExtension_eventuallyEq
    filter_upwards [hlocal] with x hx
    exact (CompactConvolution.extension_eq_raw K n μ k f κ x hx).symm
  rw [smoothDifferential_apply, heq.fderiv_eq,
    (CompactConvolution.extension_hasFDerivAt K n μ k hk f κ g).fderiv,
    ContinuousLinearMap.integral_apply
      (CompactConvolution.derivative_integrable K n μ k hk f κ g)]
  have hinter :
      (∫ y in k, ((f y) •
        ((fderiv ℝ (coordinateExtension K n κ.val)
          (CompactConvolution.leftLinear K n y
            (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n))).comp
          (CompactConvolution.leftLinear K n y)))
        ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n X) ∂μ) =
        ∫ y in k, f y * (smoothDifferential K n X κ.val).val (y⁻¹ * g) ∂μ := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      CompactConvolution.leftLinear_apply, smul_eq_mul, smoothDifferential_apply,
      map_mul, Units.val_mul, mul_assoc]
  rw [hinter]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [smoothDifferential_eq_zero_of_notMem_tsupport K n X κ.val (y⁻¹ * g)
    (hlocal.self_of_nhds y hy), mul_zero]

end Langlands.Global.ArchimedeanGL
