import Langlands.Representation.Archimedean.GardingKernelOperations

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ComplexConjugate InnerProductSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

theorem norm_apply_of_preserves_inner {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (π : G →* (E →L[ℂ] E))
    (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w) (g : G) (v : E) :
    ‖π g v‖ = ‖v‖ := by
  simp only [norm_eq_sqrt_re_inner (𝕜 := ℂ), hπu]

variable {A G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [Group G] [TopologicalSpace G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)
  (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)

variable (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ)
  (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ)

/-- The linear regularization of a smooth-vector functional by a compact smooth kernel. -/
def unitaryRegularization : smoothCompactKernels A G →ₗ[ℂ] E :=
  (InnerProductSpace.toDual ℂ E).symm.toLinearEquiv.toLinearMap.comp
    ((gardingFunctionalLinearMap μ π hπ (norm_apply_of_preserves_inner π hπu) ℓ hℓ).comp
      adjointGardingKernelEquiv.toLinearMap)

/-- Pairing with the regularized vector evaluates the functional on the adjoint average. -/
theorem inner_unitaryRegularization (f : smoothCompactKernels A G) (v : E) :
    inner ℂ (unitaryRegularization μ π hπ hπu ℓ hℓ f) v =
      ℓ (gardingIntegralLinearMap μ π hπ (adjointGardingKernel f) v) :=
  DFunLike.congr_fun ((InnerProductSpace.toDual ℂ E).apply_symm_apply
    (gardingFunctional μ π hπ (norm_apply_of_preserves_inner π hπu) ℓ hℓ
      (adjointGardingKernel f))) v

/-- The regularization can be evaluated by another smooth-vector functional. -/
def unitaryRegularizationSmooth [μ.IsInvInvariant] :
    smoothCompactKernels A G →ₗ[ℂ] smoothVectors 𝓘(ℝ, A) π :=
  (unitaryRegularization μ π hπ hπu ℓ hℓ).codRestrict _ (fun f =>
    isSmoothVector_gardingRiesz μ π hπ hπu (norm_apply_of_preserves_inner π hπu) ℓ hℓ
      (adjointGardingKernel f))

@[simp]
theorem unitaryRegularizationSmooth_coe [μ.IsInvInvariant] (f : smoothCompactKernels A G) :
    (unitaryRegularizationSmooth μ π hπ hπu ℓ hℓ f : E) =
      unitaryRegularization μ π hπ hπu ℓ hℓ f := rfl

section Translation

variable [IsTopologicalGroup G]

include hπ hπu hℓ in
/-- Left translation of the kernel translates the regularized Hilbert vector. -/
theorem unitaryRegularization_left [μ.IsMulRightInvariant] (a : G) (f : smoothCompactKernels A G) :
    unitaryRegularization μ π hπ hπu ℓ hℓ (gardingKernelLeft a f) =
      π a (unitaryRegularization μ π hπ hπu ℓ hℓ f) := by
  apply ext_inner_right ℂ
  intro v
  have hinv : π a (π a⁻¹ v) = v := by
    change (π a * π a⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hinv, hπu, inner_unitaryRegularization, inner_unitaryRegularization,
    adjointGardingKernel_left, hinv]
  apply congrArg ℓ
  apply Subtype.ext
  change (∫ x, (adjointGardingKernel f).val (x * a) • π x v ∂μ) =
    ∫ x, (adjointGardingKernel f).val x • π x (π a⁻¹ v) ∂μ
  rw [← integral_mul_right_eq_self
    (fun x => (adjointGardingKernel f).val x • π x (π a⁻¹ v)) a]
  simp only [map_mul, mul_apply_eq_comp, hinv]

/-- Left translation of the averaging kernel translates the resulting smooth vector. -/
theorem gardingIntegral_left (a : G) (f : smoothCompactKernels A G) (v : E) :
    gardingIntegralLinearMap μ π hπ (gardingKernelLeft a f) v =
      smoothRepresentation 𝓘(ℝ, A) π a (gardingIntegralLinearMap μ π hπ f v) := by
  apply Subtype.ext
  change (∫ x, f.val (a⁻¹ * x) • π x v ∂μ) = π a (∫ x, f.val x • π x v ∂μ)
  rw [← (π a).integral_comp_comm (integrable_gardingIntegrand μ π hπ f v),
    ← integral_mul_left_eq_self (fun x => f.val (a⁻¹ * x) • π x v) a]
  simp only [inv_mul_cancel_left, map_mul, mul_apply_eq_comp, map_smul]

/-- The right translation law for the regularization of a Whittaker functional. -/
theorem unitaryRegularization_right {N : Subgroup G} {χ : N →* ℂˣ}
    (hW : IsWhittakerFunctional 𝓘(ℝ, A) π N χ ℓ) (a : N) (f : smoothCompactKernels A G) :
    unitaryRegularization μ π hπ hπu ℓ hW.1 (gardingKernelRight (a : G) f) =
      conj (χ a : ℂ) • unitaryRegularization μ π hπ hπu ℓ hW.1 f := by
  apply ext_inner_right ℂ
  intro v
  rw [inner_smul_left, inner_unitaryRegularization, inner_unitaryRegularization,
    adjointGardingKernel_right, gardingIntegral_left μ π hπ, hW.2, starRingEnd_self_apply]

end Translation

variable [SigmaCompactSpace G]

/-- Equality of regularizations gives equality of the original functionals by Gårding density. -/
theorem eq_of_unitaryRegularization_eq
    (ℓ' : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ)
    (hℓ' : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ')
    (he : unitaryRegularization μ π hπ hπu ℓ hℓ =
      unitaryRegularization μ π hπ hπu ℓ' hℓ') :
    ℓ = ℓ' := by
  have hEq := Continuous.ext_on (dense_gardingAverages (A := A) μ π)
    (continuous_of_isContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ hℓ)
    (continuous_of_isContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ' hℓ') (by
      intro v hv
      obtain ⟨f, hfs, hfc, w, hw⟩ := hv
      obtain ⟨k, hk⟩ := adjointGardingKernelEquiv.surjective ⟨f, hfs, hfc⟩
      have hkv : gardingIntegralLinearMap μ π hπ (adjointGardingKernel k) w =
          DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) π v := by
        change gardingIntegralLinearMap μ π hπ (adjointGardingKernelEquiv k) w = _
        rw [hk]
        exact Subtype.ext hw.symm
      have hh := congrArg (fun (T : smoothCompactKernels A G →ₗ[ℂ] E) => inner ℂ (T k) w) he
      change inner ℂ (unitaryRegularization μ π hπ hπu ℓ hℓ k) w =
        inner ℂ (unitaryRegularization μ π hπ hπu ℓ' hℓ' k) w at hh
      rwa [inner_unitaryRegularization, inner_unitaryRegularization, hkv] at hh)
  apply LinearMap.ext
  intro v
  simpa only [LinearEquiv.apply_symm_apply] using
    congrFun hEq ((DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) π).symm v)

/-- The regularization of a nonzero continuous functional is nonzero. -/
theorem unitaryRegularization_ne_zero (hne : ℓ ≠ 0) :
    unitaryRegularization μ π hπ hπu ℓ hℓ ≠ 0 := by
  have hzero : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π 0 :=
    ⟨∅, 0, by simp⟩
  have hz : unitaryRegularization μ π hπ hπu 0 hzero = 0 := by
    apply LinearMap.ext
    intro f
    apply ext_inner_right ℂ
    intro v
    simp [inner_unitaryRegularization]
  simpa only [hz] using mt (eq_of_unitaryRegularization_eq μ π hπ hπu ℓ hℓ 0 hzero) hne

/-- Proportionality descends from regularized Hilbert vectors to the two functionals. -/
theorem proportional_of_unitaryRegularization_eq_smul
    (ℓ' : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ)
    (hℓ' : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ') (c : ℂ)
    (he : unitaryRegularization μ π hπ hπu ℓ' hℓ' =
      c • unitaryRegularization μ π hπ hπu ℓ hℓ) :
    ℓ' = conj c • ℓ := by
  have hcontinuous :=
    (continuous_iff_isContinuousOnSmoothVectors 𝓘(ℝ, A) π (conj c • ℓ)).mp
      ((continuous_of_isContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ hℓ).const_smul (conj c))
  apply eq_of_unitaryRegularization_eq μ π hπ hπu ℓ' hℓ' (conj c • ℓ) hcontinuous
  rw [he]
  apply LinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro v
  simp only [LinearMap.smul_apply, inner_smul_left, inner_unitaryRegularization, smul_eq_mul]

end Langlands.Archimedean
