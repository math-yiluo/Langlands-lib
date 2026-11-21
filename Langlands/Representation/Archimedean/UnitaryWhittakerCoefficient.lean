import Langlands.Representation.Archimedean.UnitaryRegularization
import Langlands.Representation.Unitary.IntegratedConvolutionProof

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ComplexConjugate InnerProductSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

variable {A G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)
  (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)

section Convolution

variable [SecondCountableTopology G] [SFinite μ]

include hπu in
/-- The Gårding integral of convolution is composition of the two actual averages. -/
theorem gardingIntegral_convolution (f g : smoothCompactKernels A G) (v : E) :
    gardingIntegralLinearMap μ π hπ (gardingKernelConvolution μ f g) v =
      gardingIntegralLinearMap μ π hπ f (gardingIntegralLinearMap μ π hπ g v : E) := by
  have hmeas (w : E) : AEStronglyMeasurable (fun x => π x w) μ :=
    (hπ.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hf := f.property.1.continuous.integrable_of_hasCompactSupport f.property.2 (μ := μ)
  have hg := g.property.1.continuous.integrable_of_hasCompactSupport g.property.2 (μ := μ)
  obtain ⟨_, he⟩ := Langlands.Analysis.integratedActionConvolution G E μ π
    (norm_apply_of_preserves_inner π hπu) hmeas f.val g.val hf hg
  exact Subtype.ext (DFunLike.congr_fun he v)

variable [μ.IsInvInvariant]

/-- Integrating the action moves one convolution factor off the regularization. -/
theorem unitaryRegularization_convolution
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ)
    (f g : smoothCompactKernels A G) :
    unitaryRegularizationSmooth μ π hπ hπu ℓ hℓ (gardingKernelConvolution μ f g) =
      gardingIntegralLinearMap μ π hπ f (unitaryRegularization μ π hπ hπu ℓ hℓ g) := by
  apply Subtype.ext
  apply ext_inner_right ℂ
  intro v
  change inner ℂ (unitaryRegularization μ π hπ hπu ℓ hℓ (gardingKernelConvolution μ f g)) v =
    inner ℂ (gardingIntegralLinearMap μ π hπ f (unitaryRegularization μ π hπ hπu ℓ hℓ g) : E) v
  rw [inner_unitaryRegularization, adjointGardingKernel_convolution,
    gardingIntegral_convolution μ π hπ hπu, ← inner_unitaryRegularization]
  simpa only [adjointGardingKernel_adjoint] using
    (inner_adjointGardingIntegral μ π hπ hπu (adjointGardingKernel f) _ v).symm

end Convolution

variable [μ.IsInvInvariant]
  (ℓ₀ ℓ₁ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ)
  (h₁ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ₁)

/-- Apply one smooth-vector functional to the regularization of the other. -/
def unitaryWhittakerCoefficient : smoothCompactKernels A G →ₗ[ℂ] ℂ :=
  ℓ₀.comp (unitaryRegularizationSmooth μ π hπ hπu ℓ₁ h₁)

omit [IsTopologicalGroup G] in
@[simp] theorem unitaryWhittakerCoefficient_apply (f : smoothCompactKernels A G) :
    unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ₁ h₁ f =
      ℓ₀ (unitaryRegularizationSmooth μ π hπ hπu ℓ₁ h₁ f) := rfl

/-- The generalized coefficient of an adjoint convolution is the Hilbert pairing. -/
theorem unitaryWhittakerCoefficient_convolution [SecondCountableTopology G] [SFinite μ]
    (h₀ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ₀) (f g : smoothCompactKernels A G) :
    unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ₁ h₁
      (gardingKernelConvolution μ (adjointGardingKernel f) g) =
      inner ℂ (unitaryRegularization μ π hπ hπu ℓ₀ h₀ f)
        (unitaryRegularization μ π hπ hπu ℓ₁ h₁ g) := by
  rw [unitaryWhittakerCoefficient_apply, unitaryRegularization_convolution,
    inner_unitaryRegularization]

variable {N : Subgroup G} {χ : N →* ℂˣ}

/-- The first functional gives the multiplier for left translation of the coefficient. -/
theorem unitaryWhittakerCoefficient_left [μ.IsMulRightInvariant]
    (hW₀ : IsWhittakerFunctional 𝓘(ℝ, A) π N χ ℓ₀) (a : N) (f : smoothCompactKernels A G) :
    unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ₁ h₁ (gardingKernelLeft (a : G) f) =
      (χ a : ℂ) * unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ₁ h₁ f := by
  have he : unitaryRegularizationSmooth μ π hπ hπu ℓ₁ h₁ (gardingKernelLeft (a : G) f) =
      smoothRepresentation 𝓘(ℝ, A) π (a : G) (unitaryRegularizationSmooth μ π hπ hπu ℓ₁ h₁ f) :=
    Subtype.ext (unitaryRegularization_left μ π hπ hπu ℓ₁ h₁ (a : G) f)
  rw [unitaryWhittakerCoefficient_apply, he, hW₀.2, unitaryWhittakerCoefficient_apply]

/-- The second functional gives the conjugate multiplier for right translation. -/
theorem unitaryWhittakerCoefficient_right
    (hW₁ : IsWhittakerFunctional 𝓘(ℝ, A) π N χ ℓ₁) (a : N) (f : smoothCompactKernels A G) :
    unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ₁ hW₁.1 (gardingKernelRight (a : G) f) =
      conj (χ a : ℂ) * unitaryWhittakerCoefficient μ π hπ hπu ℓ₀ ℓ₁ hW₁.1 f := by
  have he : unitaryRegularizationSmooth μ π hπ hπu ℓ₁ hW₁.1 (gardingKernelRight (a : G) f) =
      conj (χ a : ℂ) • unitaryRegularizationSmooth μ π hπ hπu ℓ₁ hW₁.1 f :=
    Subtype.ext (unitaryRegularization_right μ π hπ hπu ℓ₁ hW₁ a f)
  rw [unitaryWhittakerCoefficient_apply, he, map_smul, unitaryWhittakerCoefficient_apply, smul_eq_mul]

end Langlands.Archimedean
