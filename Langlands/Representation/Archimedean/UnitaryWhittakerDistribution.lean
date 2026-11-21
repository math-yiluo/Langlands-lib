import Langlands.Representation.Archimedean.MatrixGardingDerivatives
import Langlands.Representation.Archimedean.UnitaryWhittakerCoefficient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff Distributions Matrix.Norms.Operator InnerProductSpace

namespace Langlands.Archimedean

universe uF uE

variable {F : Type uF} [RCLike F] {n : ℕ}
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "G" => Langlands.GeneralLinear n F
local notation "D" => 𝓓(matrixUnitsOpen F n, ℂ)

variable [MeasurableSpace (Langlands.GeneralLinear n F)] [BorelSpace (Langlands.GeneralLinear n F)]
  (μ : Measure (Langlands.GeneralLinear n F)) [μ.IsHaarMeasure]
  (π : Langlands.GeneralLinear n F →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)
  (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
  (ℓ : smoothVectors (matrixModel F n) π →ₗ[ℂ] ℂ)
  (hℓ : IsContinuousOnSmoothVectors (matrixModel F n) π ℓ)

/-- The bounded functional obtained by averaging a smooth-vector functional
depends continuously in operator norm on the matrix test function. -/
def matrixGardingFunctional : D →L[ℂ] (E →L[ℂ] ℂ) where
  toLinearMap := (gardingFunctionalLinearMap μ π hπ
    (norm_apply_of_preserves_inner π hπu) ℓ hℓ).comp matrixTestFunctionKernelEquiv.toLinearMap
  cont := by
    classical
    let L : D →ₗ[ℂ] (E →L[ℂ] ℂ) := (gardingFunctionalLinearMap μ π hπ
      (norm_apply_of_preserves_inner π hπu) ℓ hℓ).comp matrixTestFunctionKernelEquiv.toLinearMap
    change Continuous L
    obtain ⟨S, C, _, hC⟩ :=
      exists_gardingFunctional_bound_on_compact μ π hπ
        (norm_apply_of_preserves_inner π hπu) ℓ hℓ
    refine (TestFunction.continuous_iff_continuous_comp L).mpr fun K hK => ?_
    let ι := TestFunction.ofSupportedInCLM (F := ℂ) (n := ⊤) ℂ hK
    change Continuous (L.comp ι.toLinearMap)
    apply continuous_of_continuousAt_zero (L.comp ι.toLinearMap)
    rw [ContinuousAt, map_zero]
    let K' : Set G := Units.val ⁻¹' (K : Set M)
    have hK' : IsCompact K' :=
      (Units.isOpenEmbedding_val (R := M)).isEmbedding.isInducing.isCompact_preimage'
        K.isCompact (hK.trans (by rw [range_val_eq_setOf_isUnit]; rfl))
    let B (Xs : List M) := (TestFunction.toBoundedContinuousFunctionCLM ℂ).comp
      ((matrixGardingTestWord Xs).comp ι)
    have hb : Continuous (fun f => (C * μ.real K') * ∑ Xs ∈ S, ‖B Xs f‖) :=
      continuous_const.mul (continuous_finsetSum _ fun Xs _ => (B Xs).continuous.norm)
    have hb₀ : Tendsto (fun f => (C * μ.real K') * ∑ Xs ∈ S, ‖B Xs f‖) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, map_zero, norm_zero, Finset.sum_const_zero, mul_zero] using
        hb.continuousAt (x := 0)
    apply squeeze_zero_norm _ hb₀
    intro f
    apply hC _ hK'
    · exact (tsupport_comp_subset_preimage _ Units.continuous_val).trans
        (preimage_mono f.tsupport_subset)
    · intro Xs _ x _
      change ‖gardingKernelWord Xs (matrixTestFunctionKernelEquiv (ι f) : G → ℂ) x‖ ≤ ‖B Xs f‖
      rw [gardingKernelWord_restrict]
      exact BoundedContinuousFunction.norm_coe_le_norm (B Xs f) x.val

@[simp]
theorem matrixGardingFunctional_apply (f : D) (v : E) :
    matrixGardingFunctional μ π hπ hπu ℓ hℓ f v =
      ℓ (gardingIntegralLinearMap μ π hπ (matrixTestFunctionKernelEquiv f) v) := rfl

variable [μ.IsInvInvariant]

/-- The finite Hilbert word expansion of a functional yields a finite sum
of ordinary Gårding averages for its regularization on matrix tests. -/
theorem unitaryRegularizationSmooth_matrix_sum (S : Finset (List M)) (w : S → E)
    (hw : ∀ v : smoothVectors 𝓘(ℝ, M) π,
      ℓ v = ∑ i : S, inner ℂ (w i) (iteratedLieDerivative 𝓘(ℝ, M) π i.val v)) (f : D) :
    unitaryRegularizationSmooth μ π hπ hπu ℓ hℓ (matrixTestFunctionKernelEquiv f) =
      ∑ i : S, gardingIntegralLinearMap μ π hπ
        (matrixTestFunctionKernelEquiv (matrixRightTestWord i.val f)) (w i) := by
  classical
  apply Subtype.ext
  apply ext_inner_right ℂ
  intro v
  change inner ℂ (unitaryRegularization μ π hπ hπu ℓ hℓ (matrixTestFunctionKernelEquiv f)) v =
    inner ℂ ((smoothVectors 𝓘(ℝ, M) π).subtype (∑ i : S, _)) v
  rw [inner_unitaryRegularization, hw, map_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  let φ := adjointGardingKernel (matrixTestFunctionKernelEquiv f)
  let ψ := matrixTestFunctionKernelEquiv (matrixRightTestWord i.val f)
  have he : iteratedLieDerivative 𝓘(ℝ, M) π i.val
      (gardingIntegralLinearMap μ π hπ φ v : E) =
        (gardingIntegralLinearMap μ π hπ (adjointGardingKernel ψ) v : E) := by
    change iteratedLieDerivative 𝓘(ℝ, M) π i.val (∫ x, φ.val x • π x v ∂μ) =
      ∫ x, (adjointGardingKernel ψ).val x • π x v ∂μ
    rw [iteratedLieDerivative_gardingIntegral μ π hπ φ.val φ.property.1 φ.property.2 v i.val,
      gardingKernelWord_adjoint_restrict]
  change inner ℂ (w i) (iteratedLieDerivative 𝓘(ℝ, M) π i.val
    (gardingIntegralLinearMap μ π hπ φ v : E)) =
      inner ℂ (gardingIntegralLinearMap μ π hπ ψ (w i) : E) v
  rw [he, ← inner_adjointGardingIntegral μ π hπ hπu (adjointGardingKernel ψ),
    adjointGardingKernel_adjoint]

variable (ℓ₀ : smoothVectors (matrixModel F n) π →ₗ[ℂ] ℂ)
  (h₀ : IsContinuousOnSmoothVectors (matrixModel F n) π ℓ₀)

/-- The Whittaker coefficient is a distribution on the open matrix units. -/
def unitaryWhittakerDistribution : D →L[ℂ] ℂ where
  toLinearMap := (unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ hℓ).comp
    matrixTestFunctionKernelEquiv.toLinearMap
  cont := by
    classical
    obtain ⟨S, w, hw⟩ := exists_inner_word_sum π ℓ hℓ
    change Continuous (fun f : D =>
      unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ hℓ (matrixTestFunctionKernelEquiv f))
    simp only [unitaryWhittakerCoefficient_apply,
      unitaryRegularizationSmooth_matrix_sum μ π hπ hπu ℓ hℓ S w hw, map_sum]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (ContinuousLinearMap.apply ℂ ℂ (w i)).continuous.comp
      ((matrixGardingFunctional μ π hπ hπu ℓ₀ h₀).continuous.comp
        (matrixRightTestWord i.val).continuous)

@[simp]
theorem unitaryWhittakerDistribution_apply (f : D) :
    unitaryWhittakerDistribution μ π hπ hπu ℓ hℓ ℓ₀ h₀ f =
      unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ hℓ (matrixTestFunctionKernelEquiv f) := rfl

end Langlands.Archimedean
