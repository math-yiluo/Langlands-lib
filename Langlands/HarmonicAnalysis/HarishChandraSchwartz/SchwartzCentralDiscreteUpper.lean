import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ProjectedQuotientPositiveForm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjectionQuotientNorm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ProjectedCoefficientClosure

/-! # The actual central-image upper inclusion from weight and finite-level estimates -/

noncomputable section

universe uG uW

open MeasureTheory

namespace Langlands.HarishChandraSchwartz

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [hT2 : T2Space Γ] [hLc : LocallyCompactSpace Γ] [hSc : SecondCountableTopology Γ]
  [MeasurableSpace Γ] [hBorG : BorelSpace Γ]
  [Nonempty (CompactOpenSubgroup Γ)]
  {A : Subgroup Γ} [A.Normal] (hAc : IsClosed (A : Set Γ))
  (hA : A ≤ Subgroup.center Γ)
  [MeasurableSpace A] [hBorA : BorelSpace A]
  (muA : Measure A) [hHaarA : muA.IsHaarMeasure] [hRightA : muA.IsMulRightInvariant]
  (muG : Measure Γ) [hHaarG : muG.IsHaarMeasure] [hRightG : muG.IsMulRightInvariant]
  [MeasurableSpace (Γ ⧸ A)] [BorelSpace (Γ ⧸ A)]
  (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure] [mu.IsInvInvariant]
  {Ξ σ : Γ → ℝ} (ht : TranslationWeights Ξ σ)
  (E : Submodule ℂ (Space Ξ σ)) (hE : IsTranslationStable ht E)
  (hw : CentralWeights muA Ξ σ) (hL : L2Weights muG Ξ σ)
  (χ : A →* ℂˣ) (hu : IsUnitaryCharacter χ)

/-- The literal quotient-L² form with its norm estimate discharged by actual
central and ambient Schwartz weights. -/
def projectedQuotientPositiveFormOfWeights (H : OpenSubgroup Γ) :
    InvariantPositiveForm
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation := by
  let hc := CentralWeights.convergesOn E muA χ hw hu
  apply projectedQuotientPositiveForm ht E hE hA muA χ hu hc H mu
  intro f
  exact exists_memLp_two_of_mem_schwartzCentralIntegralImage hAc hA muA muG mu hw hL χ hu E
    (projectedLeftSubrepresentation_mem_ambient_image ht E hE hA muA χ hc H.toSubgroup f)

include ht hE hAc hA hw hL hu hT2 hLc hSc hBorA hBorG hHaarA hRightA hHaarG hRightG

set_option maxHeartbeats 800000 in
/-- The raw central image lies in the canonical discrete-series coefficient sum
when its compact bi-level spans are finite dimensional. The invariant positive
form and all coefficient-L² inputs are constructed, not supplied. -/
theorem schwartzCentralIntegralImage_subset_discreteSeries_of_weights
    (hcof : ∀ K : OpenSubgroup Γ, ∃ L : OpenSubgroup Γ, IsCompact (L : Set Γ) ∧ L ≤ K)
    (hfinite : ∀ J : OpenSubgroup Γ, IsCompact (J : Set Γ) →
      FiniteDimensional ℂ
        (schwartzCentralIntegralSpan (schwartzBiLevel E J.toSubgroup) muA χ)) :
    schwartzCentralIntegralImage E muA χ ⊆
      (discreteSeriesCentralCoefficientSpace.{uG, max uG uW} A hA mu χ : Set (Γ → ℂ)) := by
  let hc : CentralIntegralConvergesOn E muA χ := CentralWeights.convergesOn E muA χ hw hu
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨J, hJ⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem φ)
  let H : OpenSubgroup Γ := J.1
  let R := (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation
  have ha : IsAdmissible R :=
    isAdmissible_projectedLeftSubrepresentation ht E hE hA muA χ hc H J.2 hfinite
  let b : InvariantPositiveForm R :=
    projectedQuotientPositiveFormOfWeights hAc hA muA muG mu ht E hE hw hL χ hu H
  have hCoeffL2 : ∀ e f :
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule,
      ∃ F : Γ ⧸ A → ℝ, MemLp F 2 mu ∧ ∀ g : Γ,
        F (QuotientGroup.mk g) = ‖b.inner e (R g f)‖ := by
    intro e f
    have hraw : matrixCoefficient R (b.toSmoothDual ha.1 e).val f ∈
        schwartzCentralIntegralImage E muA χ :=
      coefficientFunctionSpace_projectedLeftSubrepresentation_subset_image
        ht E hE hA muA χ hc H.toSubgroup ha
        (matrixCoefficient_mem_coefficientFunctionSpace (SmoothRep.of R ha.1)
          (b.toSmoothDual ha.1 e) f)
    exact exists_memLp_two_of_mem_schwartzCentralIntegralImage
      hAc hA muA muG mu hw hL χ hu E hraw
  let v : (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule :=
    ⟨centralProjection muA χ (φ : Γ → ℂ),
      Submodule.subset_span ⟨φ, ⟨hφ, hJ.1.isLeftInvariant⟩, rfl⟩⟩
  exact projected_mem_lifted_discreteSeries_of_positiveForm
    ht E hE hA muA χ hc H mu hcof b ha hCoeffL2 v

end Langlands.HarishChandraSchwartz
