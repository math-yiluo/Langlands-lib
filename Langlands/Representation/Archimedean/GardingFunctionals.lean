import Langlands.Representation.Archimedean.GardingKernelDerivatives

/-! # Bounded functionals of smooth compactly supported averages -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped Manifold ContDiff

namespace Langlands.Archimedean

universe uA uG uE

section Kernels

variable (A : Type uA) [NormedAddCommGroup A] [NormedSpace ℝ A]
  (G : Type uG) [TopologicalSpace G] [ChartedSpace A G]

/-- Smooth compactly supported complex kernels on a real manifold. -/
def smoothCompactKernels : Submodule ℂ (G → ℂ) where
  carrier := {φ | ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ ∧ HasCompactSupport φ}
  zero_mem' := ⟨contMDiff_const, HasCompactSupport.zero⟩
  add_mem' hφ hθ := ⟨hφ.1.add hθ.1, hφ.2.add hθ.2⟩
  smul_mem' c _φ hφ :=
    ⟨((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hφ.1,
      hφ.2.smul_left⟩

end Kernels

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  [LieGroup 𝓘(ℝ, A) ∞ G] [FiniteDimensional ℝ A] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)

include hπ in
omit [LieGroup 𝓘(ℝ, A) ∞ G] [FiniteDimensional ℝ A] [T2Space G]
    [LocallyCompactSpace G] [CompleteSpace E] in
theorem integrable_gardingIntegrand (φ : smoothCompactKernels A G) (v : E) :
    Integrable (fun g => φ.val g • π g v) μ := by
  have hv : Continuous (fun g : G => π g v) := hπ.comp (continuous_id.prodMk continuous_const)
  exact (φ.property.1.continuous.smul hv).integrable_of_hasCompactSupport φ.property.2.smul_right

/-- The actual Gårding average with a fixed kernel as a linear map into smooth vectors. -/
def gardingIntegralLinearMap (φ : smoothCompactKernels A G) :
    E →ₗ[ℂ] smoothVectors 𝓘(ℝ, A) π where
  toFun v :=
    ⟨∫ g, φ.val g • π g v ∂μ,
      isSmoothVector_gardingIntegral μ π hπ φ.val φ.property.1 φ.property.2 v⟩
  map_add' v w := by
    apply Subtype.ext
    change (∫ g, φ.val g • π g (v + w) ∂μ) =
      (∫ g, φ.val g • π g v ∂μ) + (∫ g, φ.val g • π g w ∂μ)
    simpa only [map_add, smul_add] using
      (integral_add (integrable_gardingIntegrand μ π hπ φ v)
        (integrable_gardingIntegrand μ π hπ φ w))
  map_smul' c v := by
    apply Subtype.ext
    change (∫ g, φ.val g • π g (c • v) ∂μ) = c • ∫ g, φ.val g • π g v ∂μ
    simpa only [map_smul, smul_comm (φ.val _) c] using
      (integral_smul c (fun g => φ.val g • π g v))

/-- A derivative-continuous functional after one actual Gårding average,
as a bounded functional of the initial Hilbert or Banach vector. -/
def gardingFunctional (hunitary : ∀ g v, ‖π g v‖ = ‖v‖)
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ)
    (φ : smoothCompactKernels A G) : E →L[ℂ] ℂ :=
  (ℓ.comp (gardingIntegralLinearMap μ π hπ φ)).mkContinuousOfExistsBound <| by
    obtain ⟨C, _, hc⟩ :=
      exists_norm_gardingFunctional_le μ π hπ hunitary φ.val φ.property.1 φ.property.2 ℓ hℓ
    exact ⟨C, hc⟩

@[simp]
theorem gardingFunctional_apply (hunitary : ∀ g v, ‖π g v‖ = ‖v‖)
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ)
    (φ : smoothCompactKernels A G) (v : E) :
    gardingFunctional μ π hπ hunitary ℓ hℓ φ v = ℓ (gardingIntegralLinearMap μ π hπ φ v) :=
  rfl

/-- Regularization as a complex-linear map of the test kernel. -/
def gardingFunctionalLinearMap (hunitary : ∀ g v, ‖π g v‖ = ‖v‖)
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ) :
    smoothCompactKernels A G →ₗ[ℂ] (E →L[ℂ] ℂ) where
  toFun := gardingFunctional μ π hπ hunitary ℓ hℓ
  map_add' φ θ := by
    apply ContinuousLinearMap.ext
    intro v
    change gardingFunctional μ π hπ hunitary ℓ hℓ (φ + θ) v =
      gardingFunctional μ π hπ hunitary ℓ hℓ φ v + gardingFunctional μ π hπ hunitary ℓ hℓ θ v
    simp only [gardingFunctional_apply, ← ℓ.map_add]
    apply congrArg ℓ
    apply Subtype.ext
    change (∫ g, (φ.val g + θ.val g) • π g v ∂μ) =
      (∫ g, φ.val g • π g v ∂μ) + (∫ g, θ.val g • π g v ∂μ)
    simpa only [add_smul] using
      (integral_add (integrable_gardingIntegrand μ π hπ φ v)
        (integrable_gardingIntegrand μ π hπ θ v))
  map_smul' c φ := by
    apply ContinuousLinearMap.ext
    intro v
    change gardingFunctional μ π hπ hunitary ℓ hℓ (c • φ) v =
      c • gardingFunctional μ π hπ hunitary ℓ hℓ φ v
    simp only [gardingFunctional_apply, ← ℓ.map_smul]
    apply congrArg ℓ
    apply Subtype.ext
    change (∫ g, (c * φ.val g) • π g v ∂μ) = c • ∫ g, φ.val g • π g v ∂μ
    simp only [mul_smul, integral_smul]

/-- The operator norm is controlled by finitely many `L¹` derivative seminorms. -/
theorem exists_norm_gardingFunctionalLinearMap_le (hunitary : ∀ g v, ‖π g v‖ = ‖v‖)
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ) :
    ∃ (S : Finset (List A)) (C : ℝ), 0 ≤ C ∧ ∀ φ : smoothCompactKernels A G,
      ‖gardingFunctionalLinearMap μ π hπ hunitary ℓ hℓ φ‖ ≤
        C * ∑ Xs ∈ S, ∫ x, ‖gardingKernelWord Xs φ.val x‖ ∂μ := by
  obtain ⟨S, C, hC, h⟩ := exists_gardingFunctional_L1_bound μ π hπ hunitary ℓ hℓ
  refine ⟨S, C, hC, fun φ => ContinuousLinearMap.opNorm_le_bound _ ?_ ?_⟩
  · exact mul_nonneg hC (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
  · exact h φ.val φ.property.1 φ.property.2

omit [FiniteDimensional ℝ A] [LocallyCompactSpace G] in
private theorem gardingKernelWord_integral_norm_le (Xs : List A) (φ : smoothCompactKernels A G)
    {K : Set G} (hK : IsCompact K) (hs : tsupport φ.val ⊆ K) {b : ℝ}
    (hb : ∀ x ∈ K, ‖gardingKernelWord Xs φ.val x‖ ≤ b) :
    (∫ x, ‖gardingKernelWord Xs φ.val x‖ ∂μ) ≤ μ.real K * b := by
  have hs' := (tsupport_gardingKernelWord_subset Xs φ.val).trans hs
  have hzero : ∀ x ∉ K, ‖gardingKernelWord Xs φ.val x‖ = 0 := by
    intro x hx
    by_contra hn
    exact hx (hs' (subset_closure (show x ∈ Function.support (gardingKernelWord Xs φ.val) from
      fun he => hn (he ▸ norm_zero))))
  have h := gardingKernelWord_smooth_compact Xs φ.property.1 φ.property.2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ ≤ ∫ _ in K, b ∂μ :=
      setIntegral_mono_on (h.1.continuous.norm.integrable_of_hasCompactSupport h.2.norm).integrableOn
        (integrableOn_const hK.measure_lt_top.ne) hK.measurableSet hb
    _ = _ := setIntegral_const b

/-- On each fixed compact support, uniform bounds on finitely many
genuine kernel derivatives control the bounded functional in operator norm. -/
theorem exists_gardingFunctional_bound_on_compact (hunitary : ∀ g v, ‖π g v‖ = ‖v‖)
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ) :
    ∃ (S : Finset (List A)) (C : ℝ), 0 ≤ C ∧
      ∀ (φ : smoothCompactKernels A G) {K : Set G}, IsCompact K → tsupport φ.val ⊆ K →
        ∀ b : List A → ℝ, (∀ Xs ∈ S, ∀ x ∈ K, ‖gardingKernelWord Xs φ.val x‖ ≤ b Xs) →
        ‖gardingFunctionalLinearMap μ π hπ hunitary ℓ hℓ φ‖ ≤
          C * μ.real K * ∑ Xs ∈ S, b Xs := by
  obtain ⟨S, C, hC, h⟩ := exists_norm_gardingFunctionalLinearMap_le μ π hπ hunitary ℓ hℓ
  refine ⟨S, C, hC, fun φ K hK hs b hb => ?_⟩
  calc
    _ ≤ C * ∑ Xs ∈ S, ∫ x, ‖gardingKernelWord Xs φ.val x‖ ∂μ := h φ
    _ ≤ C * ∑ Xs ∈ S, μ.real K * b Xs :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun Xs hXs =>
        gardingKernelWord_integral_norm_le μ Xs φ hK hs (hb Xs hXs)) hC
    _ = _ := by rw [← Finset.mul_sum, ← mul_assoc]

end Langlands.Archimedean
