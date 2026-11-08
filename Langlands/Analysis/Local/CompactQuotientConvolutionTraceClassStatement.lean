import Langlands.Analysis.Local.QuotientL2UnfoldingStatement
import Langlands.Analysis.OperatorIdeals
import Langlands.Representation.Unitary.IntegratedOperator

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory
open scoped CompactlySupported

/-- On a compact left coset space with a compatible quotient measure, the
left-measure convolution `g ↦ ∫ a, f₁ a * f₂ (a⁻¹ * g)` of two compactly
supported continuous weights is integrable and integrates the original right
translation action to a trace-class operator. -/
def CompactQuotientConvolutionTraceClassStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (_hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] [μG.IsMulLeftInvariant]
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (_hν : IsCompatible H μG μH ν), CompactSpace (LeftQuotient H) →
    ∀ (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
      (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
      (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG),
      (∀ (g : G) (φ : Lp ℂ 2 ν),
        (π g φ : LeftQuotient H → ℂ) =ᵐ[ν] fun q => φ (rightTranslate H g q)) →
      ∀ f₁ f₂ : C_c(G, ℂ),
        ∃ h : Integrable (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG) μG,
          Langlands.Analysis.OperatorIdeals.IsTraceClass
            (Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas
              (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG) h)

end Langlands.QuotientIntegration
