import Langlands.Analysis.DixmierMalliavin.Product
import Langlands.Analysis.Local.CompactQuotientConvolutionTraceClassStatement
import Langlands.Analysis.Local.CompactQuotientSmoothTraceClassStatement
import Langlands.Analysis.TraceClassIdealProof

/-!
# Trace class of smooth weights from trace class of convolution products

`compactQuotientSmoothTraceClass_of_convolution` and
`compactQuotientProductSmoothTraceClass_of_convolution` prove the two statements of
`CompactQuotientSmoothTraceClassStatement` from `CompactQuotientConvolutionTraceClassStatement`,
through the Dixmier–Malliavin factorization and the additivity of the integrated operator in the
weight (`Langlands.Analysis.integratedIsometricAction_add`, with `isTraceClass_add`).
-/

noncomputable section

universe uE uG uA uB uH

open MeasureTheory
open scoped CompactlySupported Manifold ContDiff

namespace Langlands.Analysis

section Additivity

variable {G : Type uG} [Group G] [MeasurableSpace G]
  {E : Type uH} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure G) (π : G →* (E →L[ℂ] E))
  (hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
  (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ)

/-- The integrated operator depends only on the weight, not on the integrability proof. -/
theorem integratedIsometricAction_congr {f₁ f₂ : G → ℂ} (hf : f₁ = f₂)
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) :
    integratedIsometricAction μ π hπnorm hπmeas f₁ h₁ =
      integratedIsometricAction μ π hπnorm hπmeas f₂ h₂ := by
  subst hf
  rfl

/-- The integrated operator is additive in the weight. -/
theorem integratedIsometricAction_add (f₁ f₂ : G → ℂ) (h₁ : Integrable f₁ μ)
    (h₂ : Integrable f₂ μ) :
    integratedIsometricAction μ π hπnorm hπmeas (f₁ + f₂) (h₁.add h₂) =
      integratedIsometricAction μ π hπnorm hπmeas f₁ h₁ +
        integratedIsometricAction μ π hπnorm hπmeas f₂ h₂ := by
  ext x
  simp only [integratedIsometricAction_apply, add_apply, Pi.add_apply,
    add_smul]
  exact integral_add (isometricActionIntegrand_integrable μ π hπnorm hπmeas f₁ h₁ x)
    (isometricActionIntegrand_integrable μ π hπnorm hπmeas f₂ h₂ x)

/-- The integrated operator of the zero weight is `0`. -/
theorem integratedIsometricAction_zero :
    integratedIsometricAction μ π hπnorm hπmeas 0 (integrable_zero G ℂ μ) = 0 := by
  ext x
  simp

/-- A finite sum of integrable weights whose integrated operators are trace class is integrable,
and its integrated operator is trace class. -/
theorem exists_isTraceClass_integratedIsometricAction_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → G → ℂ)
    (hf : ∀ i ∈ s, ∃ h : Integrable (f i) μ,
      OperatorIdeals.IsTraceClass (integratedIsometricAction μ π hπnorm hπmeas (f i) h)) :
    ∃ h : Integrable (∑ i ∈ s, f i) μ,
      OperatorIdeals.IsTraceClass
        (integratedIsometricAction μ π hπnorm hπmeas (∑ i ∈ s, f i) h) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : ∑ i ∈ (∅ : Finset ι), f i = 0 := Finset.sum_empty
    have hI : Integrable (∑ i ∈ (∅ : Finset ι), f i) μ := by rw [e]; exact integrable_zero G ℂ μ
    refine ⟨hI, ?_⟩
    rw [integratedIsometricAction_congr μ π hπnorm hπmeas e hI (integrable_zero G ℂ μ),
      integratedIsometricAction_zero]
    exact OperatorIdeals.isTraceClass_zero
  | insert a s ha ih =>
    obtain ⟨h₁, t₁⟩ := hf a (Finset.mem_insert_self a s)
    obtain ⟨h₂, t₂⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have e : ∑ i ∈ insert a s, f i = f a + ∑ i ∈ s, f i := Finset.sum_insert ha
    have hI : Integrable (∑ i ∈ insert a s, f i) μ := by rw [e]; exact h₁.add h₂
    refine ⟨hI, ?_⟩
    rw [integratedIsometricAction_congr μ π hπnorm hπmeas e hI (h₁.add h₂),
      integratedIsometricAction_add μ π hπnorm hπmeas (f a) _ h₁ h₂]
    exact OperatorIdeals.isTraceClass_add _ _ t₁ t₂

end Additivity

end Langlands.Analysis

namespace Langlands.QuotientIntegration

open Langlands.Analysis

/-- `CompactQuotientSmoothTraceClassStatement` follows from
`CompactQuotientConvolutionTraceClassStatement`: write the smooth weight as a finite sum of
convolutions (`Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution`) and add the
trace-class operators of the pieces. -/
theorem compactQuotientSmoothTraceClass_of_convolution
    (h : CompactQuotientConvolutionTraceClassStatement.{uG}) :
    CompactQuotientSmoothTraceClassStatement.{uE, uG, uA} := by
  intro E G _ _ _ _ _ _ _ _ _ _ _ 𝔸 _ _ _ _ ρ hρ H hH _ _ μH _ _ _ _ _ μG _ ν _ hν hcpt π hπnorm
    hπmeas hπ f
  have : SecondCountableTopology 𝔸ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : SecondCountableTopology G := hρ.isClosedEmbedding.isEmbedding.secondCountableTopology
  obtain ⟨n, φ, ψ, -, hsum⟩ :=
    Archimedean.exists_eq_sum_gardingKernelConvolution hρ μG Filter.univ_mem f
  let toCc : Archimedean.smoothCompactKernels E G → C_c(G, ℂ) := fun u =>
    ⟨⟨u.val, u.property.1.continuous⟩, u.property.2⟩
  have hf : f.val = ∑ i, fun g => ∫ a, toCc (φ i) a * toCc (ψ i) (a⁻¹ * g) ∂μG := by
    conv_lhs => rw [hsum]
    rw [Submodule.coe_sum]
    rfl
  obtain ⟨hI, htc⟩ := exists_isTraceClass_integratedIsometricAction_finsetSum μG π hπnorm hπmeas
    Finset.univ _ fun i _ => h H hH μH μG ν hν hcpt π hπnorm hπmeas hπ (toCc (φ i)) (toCc (ψ i))
  refine ⟨hf ▸ hI, ?_⟩
  rwa [integratedIsometricAction_congr μG π hπnorm hπmeas hf (hf ▸ hI) hI]

/-- `CompactQuotientProductSmoothTraceClassStatement` follows from
`CompactQuotientConvolutionTraceClassStatement`, through the factorization on products
(`Langlands.Analysis.DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod`). -/
theorem compactQuotientProductSmoothTraceClass_of_convolution
    (h : CompactQuotientConvolutionTraceClassStatement.{max uG uB}) :
    CompactQuotientProductSmoothTraceClassStatement.{uE, uG, uA, uB} := by
  intro E A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 𝔸 _ _ _ _ ρ hρ H hH _ _ μH _ _ _ _ _ μG _ ν _
    hν hcpt π hπnorm hπmeas hπ f hf V hVo hVc hfV
  have : SecondCountableTopology 𝔸ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : SecondCountableTopology A := hρ.isClosedEmbedding.isEmbedding.secondCountableTopology
  obtain ⟨n, φ, ψ, -, hsum⟩ :=
    DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod hρ μG f hf V hVo hVc hfV
  have hf' : (f : A × B → ℂ) = ∑ i, fun g => ∫ a, φ i a * ψ i (a⁻¹ * g) ∂μG := by
    funext x
    rw [hsum x, Finset.sum_apply]
    rfl
  obtain ⟨hI, htc⟩ := exists_isTraceClass_integratedIsometricAction_finsetSum μG π hπnorm hπmeas
    Finset.univ _ fun i _ => h H hH μH μG ν hν hcpt π hπnorm hπmeas hπ (φ i) (ψ i)
  refine ⟨hf' ▸ hI, ?_⟩
  rwa [integratedIsometricAction_congr μG π hπnorm hπmeas hf' (hf' ▸ hI) hI]

end Langlands.QuotientIntegration
