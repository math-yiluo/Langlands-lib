import Langlands.Global.ArchimedeanCompactKernelAverage
import Langlands.Global.ArchimedeanKernelConjugationAverageProof

/-! # Actual smoothing operators and compact intertwining -/

noncomputable section
universe u
open MeasureTheory Set Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.CompactKernelAverage

open DerivativeSmoothFunctions

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}
variable [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
variable (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]

/-- The actual smooth lift of raw convolution as a linear map of its input. -/
def smoothingLM (κ : SmoothCompactKernel K n) :
    DerivativeSmoothFunctions K n →ₗ[ℂ] DerivativeSmoothFunctions K n :=
  CompactIndexAverage.averageLM (inclusion κ) (measure μ κ) (weight κ)

theorem smoothingLM_eq_rawConvolution (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    (toSmooth K n (smoothingLM μ κ f)).val x =
      rawConvolution K n μ (toContinuousMap K n (toSmooth K n f)) κ x :=
  average_eq_rawConvolution μ κ f x

theorem smoothingLM_eq_integral (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    (toSmooth K n (smoothingLM μ κ f)).val x =
      ∫ g, κ.val.val g⁻¹ * (toSmooth K n f).val (x * g) ∂μ :=
  average_eq_integral μ κ f x

theorem smoothingLM_mem_closed_groupOrbit (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) :
    smoothingLM μ κ f ∈
      (Submodule.span ℂ (range fun g : InfiniteAdelicGL K n =>
        rightAction K n g f)).topologicalClosure :=
  average_mem_closed_groupOrbit μ κ f

/-- The smooth lift is linear also in the actual compact smooth kernel. -/
def smoothingBilinear :
    SmoothCompactKernel K n →ₗ[ℂ]
      DerivativeSmoothFunctions K n →ₗ[ℂ] DerivativeSmoothFunctions K n where
  toFun := smoothingLM μ
  map_add' κ η := by
    apply LinearMap.ext
    intro f
    apply (toSmooth K n).injective
    apply Subtype.ext
    funext x
    change (toSmooth K n (smoothingLM μ (κ + η) f)).val x =
      (toSmooth K n (smoothingLM μ κ f)).val x +
        (toSmooth K n (smoothingLM μ η f)).val x
    simp only [smoothingLM_eq_rawConvolution]
    exact congrFun (rawConvolution_add_right K n μ
      (toContinuousMap K n (toSmooth K n f)) κ η) x
  map_smul' z κ := by
    apply LinearMap.ext
    intro f
    apply (toSmooth K n).injective
    apply Subtype.ext
    funext x
    change (toSmooth K n (smoothingLM μ (z • κ) f)).val x =
      z * (toSmooth K n (smoothingLM μ κ f)).val x
    simp only [smoothingLM_eq_rawConvolution]
    exact congrFun (rawConvolution_smul_right K n μ z
      (toContinuousMap K n (toSmooth K n f)) κ) x

@[simp]
theorem smoothingBilinear_apply (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) :
    smoothingBilinear μ κ f = smoothingLM μ κ f := rfl

/-- Compact conjugation invariance of the kernel makes the actual smoothing
operator commute with every actual compact right translation. -/
theorem smoothingLM_compactAction (κ : SmoothCompactKernel K n)
    (hκ : ∀ (k : standardInfiniteCompact K n) (g : InfiniteAdelicGL K n),
      κ.val.val (k.val⁻¹ * g * k.val) = κ.val.val g)
    (k : standardInfiniteCompact K n) (f : DerivativeSmoothFunctions K n) :
    smoothingLM μ κ (compactAction K n k f) =
      compactAction K n k (smoothingLM μ κ f) := by
  apply (toSmooth K n).injective
  apply Subtype.ext
  funext x
  change (toSmooth K n (smoothingLM μ κ (compactAction K n k f))).val x =
    (toSmooth K n (smoothingLM μ κ f)).val (x * k.val)
  rw [smoothingLM_eq_integral, smoothingLM_eq_integral]
  simp only [compactAction_apply, toSmooth_rightAction_val]
  let φ : InfiniteAdelicGL K n → ℂ :=
    fun g => κ.val.val g⁻¹ * (toSmooth K n f).val ((x * k.val) * g)
  have hφ : HasCompactSupport φ :=
    (κ.property.comp_homeomorph (Homeomorph.inv (InfiniteAdelicGL K n))).mul_right
  calc
    (∫ g, κ.val.val g⁻¹ * (toSmooth K n f).val ((x * g) * k.val) ∂μ) =
        ∫ g, φ (k.val⁻¹ * g * k.val) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      dsimp only [φ]
      have hinv : (k.val⁻¹ * g * k.val)⁻¹ = k.val⁻¹ * g⁻¹ * k.val := by group
      have hmul : (x * k.val) * (k.val⁻¹ * g * k.val) = (x * g) * k.val := by
        group
      rw [hinv, hκ k g⁻¹, hmul]
    _ = ∫ g, φ g ∂μ :=
      KernelConjugationAverage.integral_conj_of_mem_compact μ
        (standardInfiniteCompact K n) (isCompact_standardInfiniteCompact K n)
        k.property hφ

/-- The compact-equivariant map supplied by a compact-central smooth kernel. -/
def smoothingIntertwining (κ : SmoothCompactKernel K n)
    (hκ : ∀ (k : standardInfiniteCompact K n) (g : InfiniteAdelicGL K n),
      κ.val.val (k.val⁻¹ * g * k.val) = κ.val.val g) :
    (compactAction K n).IntertwiningMap (compactAction K n) where
  toLinearMap := smoothingLM μ κ
  isIntertwining' k := by
    ext f
    exact smoothingLM_compactAction μ κ hκ k f

/-- Every actual compact isotypic span is preserved by compact-central
smoothing, by composition of its defining algebraic intertwiners. -/
theorem smoothingLM_mem_isotypicSpan (κ : SmoothCompactKernel K n)
    (hκ : ∀ (k : standardInfiniteCompact K n) (g : InfiniteAdelicGL K n),
      κ.val.val (k.val⁻¹ * g * k.val) = κ.val.val g)
    (τ : ContinuousCompactRep K n) {f : DerivativeSmoothFunctions K n}
    (hf : f ∈ isotypicSpan τ) :
    smoothingLM μ κ f ∈ isotypicSpan τ := by
  have hle : isotypicSpan τ ≤ (isotypicSpan τ).comap (smoothingLM μ κ) := by
    apply (isotypicSpan_le_iff τ _).mpr
    intro e
    rintro _ ⟨v, rfl⟩
    exact range_le_isotypicSpan τ ((smoothingIntertwining μ κ hκ).comp e)
      ⟨v, rfl⟩
  exact hle hf

/-- Every finite selected sum of actual compact types is preserved. -/
theorem smoothingLM_mem_selectedTypeSum {ι : Type*}
    (κ : SmoothCompactKernel K n)
    (hκ : ∀ (k : standardInfiniteCompact K n) (g : InfiniteAdelicGL K n),
      κ.val.val (k.val⁻¹ * g * k.val) = κ.val.val g)
    (s : Finset ι) (σ : ι → CompactType K n) {f : DerivativeSmoothFunctions K n}
    (hf : f ∈ selectedTypeSum s σ) :
    smoothingLM μ κ f ∈ selectedTypeSum s σ := by
  have hle : selectedTypeSum s σ ≤
      (selectedTypeSum s σ).comap (smoothingLM μ κ) := by
    apply iSup_le
    intro i
    apply iSup_le
    intro hi v hv
    exact isotypicSpan_le_selectedIsotypicSum
      (fun j => (σ j).toContinuousCompactRep) hi
      (smoothingLM_mem_isotypicSpan μ κ hκ (σ i).toContinuousCompactRep hv)
  exact hle hf

end Langlands.Global.ArchimedeanGL.CompactKernelAverage
