import Langlands.Analysis.Local.QuotientL2UnfoldingStatement

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory
open scoped CompactlySupported Pointwise

/-- On a left coset space with a compatible quotient measure, every compactly
supported continuous weight `f` has a continuous family of `L²` kernel vectors
`v x` whose pairing with every class `φ` is the absolutely convergent integral
`∫ f(a) φ(H (x a)) da`, with an explicit norm bound at each `x` by a uniform
bound of `‖f‖`, the `L¹` norm of `f` and the subgroup measure of `x S x⁻¹`,
`S = supp f · (supp f)⁻¹`. -/
def QuotientConvolutionKernelStatement : Prop :=
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
    (_hν : IsCompatible H μG μH ν) (f : C_c(G, ℂ)),
    ∃ v : G → Lp ℂ 2 ν, Continuous v ∧
      (∀ (x : G) (φ : Lp ℂ 2 ν),
        Integrable (fun a => f a * φ (leftQuotientMap H (x * a))) μG ∧
          inner ℂ (v x) φ = ∫ a, f a * φ (leftQuotientMap H (x * a)) ∂μG) ∧
      ∀ (x : G) (M : ℝ), (∀ a, ‖f a‖ ≤ M) →
        ‖v x‖ ^ 2 ≤ M * (∫ a, ‖f a‖ ∂μG) *
          μH.real (Subtype.val ⁻¹'
            ((fun s => x * s * x⁻¹) '' (tsupport f * (tsupport f)⁻¹)))

end Langlands.QuotientIntegration
