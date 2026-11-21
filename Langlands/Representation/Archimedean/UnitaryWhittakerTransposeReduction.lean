import Langlands.Representation.Archimedean.UnitaryWhittakerCoefficient
import Langlands.Representation.Archimedean.UnitaryRegularizationPairing

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ComplexConjugate InnerProductSpace

namespace Langlands.Archimedean

variable {A G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace A G]
  [LieGroup 𝓘(ℝ, A) ∞ G]
  (e : G ≃ₜ G) (he : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ e)
  (he' : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ e.symm)

omit [IsTopologicalGroup G] in
/-- Conjugate pullback by transpose followed by pointwise inversion. -/
def conjugateTransposeGardingKernel : smoothCompactKernels A G ≃ₗ⋆[ℂ] smoothCompactKernels A G :=
  adjointGardingKernelEquiv.trans (gardingKernelPullbackEquiv e he he')

omit [IsTopologicalGroup G] in
theorem conjugateTransposeGardingKernel_apply (f : smoothCompactKernels A G) (x : G) :
    (conjugateTransposeGardingKernel e he he' f).val x = conj (f.val (e x)⁻¹) := rfl

variable (θ : G ≃* G) (hθ : ∀ x, (e x)⁻¹ = θ x)

include hθ in
theorem conjugateTransposeGardingKernel_left (a : G) (f : smoothCompactKernels A G) :
    conjugateTransposeGardingKernel e he he' (gardingKernelLeft a f) =
      gardingKernelLeft (θ.symm a) (conjugateTransposeGardingKernel e he he' f) := by
  apply Subtype.ext
  funext x
  simp only [conjugateTransposeGardingKernel_apply, gardingKernelLeft_apply, hθ,
    map_mul, map_inv, MulEquiv.apply_symm_apply]

variable [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (hμθ : MeasurePreserving θ μ μ)

include hθ hμθ in
/-- Transpose on an adjoint convolution agrees with conjugate transpose on the factors
in reverse order. -/
theorem transpose_adjointGardingKernel_convolution (f g : smoothCompactKernels A G) :
    gardingKernelPullback e he (gardingKernelConvolution μ (adjointGardingKernel f) g) =
      gardingKernelConvolution μ (adjointGardingKernel (conjugateTransposeGardingKernel e he he' g))
        (conjugateTransposeGardingKernel e he he' f) := by
  apply Subtype.ext
  funext x
  let m := (e.trans (Homeomorph.inv G)).trans (Homeomorph.mulLeft (e x))
  have hm : MeasurePreserving m.toMeasurableEquiv μ μ := by
    have hx : (m.toMeasurableEquiv : G → G) = fun b => e x * θ b :=
      funext fun b => congrArg (e x * ·) (hθ b)
    rw [hx]
    exact (measurePreserving_mul_left μ (e x)).comp hμθ
  change (∫ a, conj (f.val a⁻¹) * g.val (a⁻¹ * e x) ∂μ) = _
  rw [← hm.integral_comp' (fun a => conj (f.val a⁻¹) * g.val (a⁻¹ * e x))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro b
  change conj (f.val (e x * (e b)⁻¹)⁻¹) * g.val ((e x * (e b)⁻¹)⁻¹ * e x) =
    conj ((conjugateTransposeGardingKernel e he he' g).val b⁻¹) *
      (conjugateTransposeGardingKernel e he he' f).val (b⁻¹ * x)
  simp only [mul_inv_rev, conjugateTransposeGardingKernel_apply, hθ, map_inv, map_mul,
    starRingEnd_self_apply]
  have hx : θ x * e x = 1 := by rw [← hθ x, inv_mul_cancel]
  rw [← hθ b, inv_inv, mul_assoc, hx, mul_one, mul_comm]

variable [FiniteDimensional ℝ A] [SecondCountableTopology G] [SFinite μ]
  [μ.IsInvInvariant] [μ.IsMulRightInvariant]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)
  (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
  (hirr : IsTopologicallyIrreducible π)

include he' hθ hμθ hirr in
/-- Transposition of the two actual generalized coefficients gives proportionality
of the original functionals on all smooth vectors. -/
theorem proportional_of_unitaryWhittakerCoefficient_transpose
    (ℓ₀ ℓ₁ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ)
    (h₀ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ₀)
    (h₁ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ₁) (hne : ℓ₀ ≠ 0)
    (hsym₀ : ∀ f, unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ₀ h₀
      (gardingKernelPullback e he f) = unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ₀ h₀ f)
    (hsym₁ : ∀ f, unitaryWhittakerCoefficient μ π hπ hπu ℓ₁ ℓ₀ h₀
      (gardingKernelPullback e he f) = unitaryWhittakerCoefficient μ π hπ hπu ℓ₁ ℓ₀ h₀ f) :
    ∃ c : ℂ, ℓ₁ = c • ℓ₀ := by
  let J := conjugateTransposeGardingKernel e he he'
  let S₀ := unitaryRegularization μ π hπ hπu ℓ₀ h₀
  let S₁ := unitaryRegularization μ π hπ hπu ℓ₁ h₁
  have hpair (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ)
      (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ)
      (hsym : ∀ f, unitaryWhittakerCoefficient μ π hπ hπu ℓ ℓ₀ h₀
        (gardingKernelPullback e he f) = unitaryWhittakerCoefficient μ π hπ hπu ℓ ℓ₀ h₀ f)
      (f g : smoothCompactKernels A G) :
      inner ℂ (unitaryRegularization μ π hπ hπu ℓ hℓ f) (S₀ g) =
        inner ℂ (unitaryRegularization μ π hπ hπu ℓ hℓ (J g)) (S₀ (J f)) := by
    have ht := hsym (gardingKernelConvolution μ (adjointGardingKernel f) g)
    rw [transpose_adjointGardingKernel_convolution e he he' θ hθ μ hμθ,
      unitaryWhittakerCoefficient_convolution _ _ _ _ _ _ _ hℓ,
      unitaryWhittakerCoefficient_convolution _ _ _ _ _ _ _ hℓ] at ht
    exact ht.symm
  obtain ⟨c, hc⟩ := proportional_of_unitary_regularization_symmetry π hπu hirr θ.symm J
    (fun a f => gardingKernelLeft a f) (conjugateTransposeGardingKernel_left e he he' θ hθ)
    S₀ S₁ (unitaryRegularization_ne_zero μ π hπ hπu ℓ₀ h₀ hne)
    (unitaryRegularization_left μ π hπ hπu ℓ₀ h₀)
    (unitaryRegularization_left μ π hπ hπu ℓ₁ h₁)
    (hpair ℓ₀ h₀ hsym₀) (hpair ℓ₁ h₁ hsym₁)
  exact ⟨conj c, proportional_of_unitaryRegularization_eq_smul μ π hπ hπu ℓ₀ h₀ ℓ₁ h₁ c hc⟩

end Langlands.Archimedean
