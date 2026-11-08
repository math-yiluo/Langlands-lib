import Langlands.Analysis.Local.QuotientL2UnfoldingStatement
import Langlands.Representation.Unitary.IntegratedOperator

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory
open scoped CompactlySupported Pointwise

/-- On a left coset space with a compatible quotient measure, the original
right translation action integrates every compactly supported continuous
weight to an operator whose values are almost everywhere equal to continuous
functions, with a pointwise bound at each coset `H x` by the norm of the
class, a uniform bound and the `L¹` norm of the weight, and the subgroup
measure of `x S x⁻¹`, `S = supp f · (supp f)⁻¹`. -/
def QuotientIntegratedContinuousRepresentativeStatement : Prop :=
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
    (_hν : IsCompatible H μG μH ν)
    (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
    (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG),
    (∀ (g : G) (φ : Lp ℂ 2 ν),
      (π g φ : LeftQuotient H → ℂ) =ᵐ[ν] fun q => φ (rightTranslate H g q)) →
    ∀ (f : C_c(G, ℂ)) (hf : Integrable f μG) (φ : Lp ℂ 2 ν),
      ∃ ψ : LeftQuotient H → ℂ, Continuous ψ ∧
        (Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f hf φ :
          LeftQuotient H → ℂ) =ᵐ[ν] ψ ∧
        ∀ (x : G) (M : ℝ), (∀ a, ‖f a‖ ≤ M) →
          ‖ψ (leftQuotientMap H x)‖ ^ 2 ≤ M * (∫ a, ‖f a‖ ∂μG) *
            μH.real (Subtype.val ⁻¹'
              ((fun s => x * s * x⁻¹) '' (tsupport f * (tsupport f)⁻¹))) * ‖φ‖ ^ 2

end Langlands.QuotientIntegration
