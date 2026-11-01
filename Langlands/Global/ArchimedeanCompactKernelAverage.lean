import Langlands.Global.ArchimedeanCompactIndexApproximation
import Langlands.Global.ArchimedeanConvolution
import Mathlib.MeasureTheory.Group.Integral

/-! # Raw convolution as an actual compact-index smooth average -/

noncomputable section
universe u
open MeasureTheory Set Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.CompactKernelAverage

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

/-- The inverse image of the actual kernel support under inversion. -/
def inverseSupport (κ : SmoothCompactKernel K n) : Set (InfiniteAdelicGL K n) :=
  (fun g => g⁻¹) ⁻¹' tsupport κ.val.val

theorem isCompact_inverseSupport (κ : SmoothCompactKernel K n) :
    IsCompact (inverseSupport κ) :=
  (Homeomorph.inv (InfiniteAdelicGL K n)).isCompact_preimage.mpr κ.property

theorem isClosed_inverseSupport (κ : SmoothCompactKernel K n) :
    IsClosed (inverseSupport κ) :=
  (isCompact_inverseSupport κ).isClosed

instance compactSpace_inverseSupport (κ : SmoothCompactKernel K n) :
    CompactSpace (inverseSupport κ) :=
  isCompact_iff_compactSpace.mp (isCompact_inverseSupport κ)

/-- The compact family consists of the actual group elements in inverse support. -/
def inclusion (κ : SmoothCompactKernel K n) :
    C(inverseSupport κ, InfiniteAdelicGL K n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The scalar weight is the original kernel evaluated on the inverse. -/
def weight (κ : SmoothCompactKernel K n) : C(inverseSupport κ, ℂ) :=
  ⟨fun j => κ.val.val (j.val⁻¹),
    (continuous K n κ.val).comp (continuous_subtype_val.inv)⟩

theorem kernel_eq_zero_off_inverseSupport (κ : SmoothCompactKernel K n)
    (g : InfiniteAdelicGL K n) (hg : g ∉ inverseSupport κ) :
    κ.val.val g⁻¹ = 0 :=
  image_eq_zero_of_notMem_tsupport hg

variable [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
variable (μ : Measure (InfiniteAdelicGL K n))

/-- The finite measure on the compact subtype is induced from the restriction. -/
def measure (κ : SmoothCompactKernel K n) : Measure (inverseSupport κ) :=
  (μ.restrict (inverseSupport κ)).comap Subtype.val

instance finiteMeasure [IsFiniteMeasureOnCompacts μ] (κ : SmoothCompactKernel K n) :
    IsFiniteMeasure (measure μ κ) := by
  let : IsFiniteMeasure (μ.restrict (inverseSupport κ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_inverseSupport κ).measure_lt_top.ne
  exact inferInstanceAs
    (IsFiniteMeasure ((μ.restrict (inverseSupport κ)).comap Subtype.val))

/-- Compact-subtype integrals recover full integrals for functions vanishing off
the inverse support. This identity does not invoke inversion invariance. -/
theorem integral_eq_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : SmoothCompactKernel K n) (F : InfiniteAdelicGL K n → E)
    (hF : ∀ g, g ∉ inverseSupport κ → F g = 0) :
    (∫ j : inverseSupport κ, F j.val ∂measure μ κ) = ∫ g, F g ∂μ := by
  have hs : MeasurableSet (inverseSupport κ) :=
    (isClosed_inverseSupport κ).measurableSet
  rw [measure, integral_subtype_comap hs F, Measure.restrict_restrict hs, inter_self]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hF

theorem integral_weight (κ : SmoothCompactKernel K n) :
    (∫ j, weight κ j ∂measure μ κ) = ∫ g, κ.val.val g⁻¹ ∂μ :=
  integral_eq_full μ κ (fun g => κ.val.val g⁻¹)
    (kernel_eq_zero_off_inverseSupport κ)

omit [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)] in
/-- Nonnegative real kernel values have equal real part and complex norm. -/
theorem norm_weight_eq_re (κ : SmoothCompactKernel K n)
    (hκ : ∀ g, 0 ≤ (κ.val.val g).re ∧ (κ.val.val g).im = 0)
    (j : inverseSupport κ) :
    ‖weight κ j‖ = (weight κ j).re := by
  have h := hκ j.val⁻¹
  have hz : κ.val.val j.val⁻¹ = ((κ.val.val j.val⁻¹).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using h.2
  change ‖κ.val.val j.val⁻¹‖ = _
  calc
    ‖κ.val.val j.val⁻¹‖ = ‖((κ.val.val j.val⁻¹).re : ℂ)‖ := congrArg norm hz
    _ = (κ.val.val j.val⁻¹).re := by
      rw [Complex.norm_real, Real.norm_of_nonneg h.1]

theorem integral_norm_weight [IsFiniteMeasureOnCompacts μ] (κ : SmoothCompactKernel K n)
    (hκ : ∀ g, 0 ≤ (κ.val.val g).re ∧ (κ.val.val g).im = 0)
    (hnorm : (∫ g, κ.val.val g⁻¹ ∂μ) = 1) :
    (∫ j, ‖weight κ j‖ ∂measure μ κ) = 1 := by
  have hi : Integrable (fun j => weight κ j) (measure μ κ) :=
    (weight κ).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [norm_weight_eq_re κ hκ]
  have hre : (∫ j, (weight κ j).re ∂measure μ κ) =
      (∫ j, weight κ j ∂measure μ κ).re :=
    Complex.reCLM.integral_comp_comm hi
  rw [hre, integral_weight μ κ, hnorm]
  rfl

variable [μ.IsHaarMeasure]

/-- Every compact-kernel average belongs to the closed span of the full
actual group orbit of its input. -/
theorem average_mem_closed_groupOrbit (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) :
    CompactIndexAverage.averageLM (inclusion κ) (measure μ κ) (weight κ) f ∈
      (Submodule.span ℂ (range fun g : InfiniteAdelicGL K n =>
        DerivativeSmoothFunctions.rightAction K n g f)).topologicalClosure := by
  apply Submodule.topologicalClosure_mono
    (s := Submodule.span ℂ (range fun j : inverseSupport κ =>
      DerivativeSmoothFunctions.rightAction K n (inclusion κ j) f)) ?_
    (CompactIndexAverage.average_mem_closed_orbit
      (inclusion κ) (measure μ κ) (weight κ) f)
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span ⟨inclusion κ j, rfl⟩

/-- The scalar formula for the actual smooth average after removing the
compact inverse-support restriction. -/
theorem average_eq_integral (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    (DerivativeSmoothFunctions.toSmooth K n
      (CompactIndexAverage.averageLM (inclusion κ) (measure μ κ) (weight κ) f)).val x =
        ∫ g, κ.val.val g⁻¹ * (DerivativeSmoothFunctions.toSmooth K n f).val (x * g) ∂μ := by
  change (∫ j : inverseSupport κ,
    κ.val.val j.val⁻¹ * (DerivativeSmoothFunctions.toSmooth K n f).val (x * j.val)
      ∂measure μ κ) = _
  exact integral_eq_full μ κ
    (fun g => κ.val.val g⁻¹ * (DerivativeSmoothFunctions.toSmooth K n f).val (x * g))
    (fun g hg => by rw [kernel_eq_zero_off_inverseSupport κ g hg, zero_mul])

/-- Left translation, with no use of invariance under inversion, identifies the
actual smooth compact-index average with the published raw convolution. -/
theorem average_eq_rawConvolution (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    (DerivativeSmoothFunctions.toSmooth K n
      (CompactIndexAverage.averageLM (inclusion κ) (measure μ κ) (weight κ) f)).val x =
      rawConvolution K n μ
        (toContinuousMap K n (DerivativeSmoothFunctions.toSmooth K n f)) κ x := by
  rw [average_eq_integral μ κ f x]
  calc
    (∫ g, κ.val.val g⁻¹ * (DerivativeSmoothFunctions.toSmooth K n f).val (x * g) ∂μ) =
        ∫ g, (DerivativeSmoothFunctions.toSmooth K n f).val (x * g) *
          κ.val.val ((x * g)⁻¹ * x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact mul_comm (κ.val.val g⁻¹)
        ((DerivativeSmoothFunctions.toSmooth K n f).val (x * g))
    _ = rawConvolution K n μ
        (toContinuousMap K n (DerivativeSmoothFunctions.toSmooth K n f)) κ x :=
      integral_mul_left_eq_self
        (fun y => (DerivativeSmoothFunctions.toSmooth K n f).val y * κ.val.val (y⁻¹ * x)) x

/-- The published raw convolution has an actual smooth lift in the closed
full group orbit span, without any compact-finiteness hypothesis. -/
theorem exists_smoothLift_mem_closed_groupOrbit (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) :
    ∃ F : DerivativeSmoothFunctions K n,
      F ∈ (Submodule.span ℂ (range fun g : InfiniteAdelicGL K n =>
        DerivativeSmoothFunctions.rightAction K n g f)).topologicalClosure ∧
      ∀ x : InfiniteAdelicGL K n,
        (DerivativeSmoothFunctions.toSmooth K n F).val x =
          rawConvolution K n μ
            (toContinuousMap K n (DerivativeSmoothFunctions.toSmooth K n f)) κ x :=
  ⟨_, average_mem_closed_groupOrbit μ κ f, average_eq_rawConvolution μ κ f⟩

end Langlands.Global.ArchimedeanGL.CompactKernelAverage
