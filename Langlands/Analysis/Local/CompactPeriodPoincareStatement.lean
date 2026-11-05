import Langlands.Analysis.Local.QuotientAverageReal
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory Set
open scoped CompactlySupported

universe uG uX

/-- Compact-domain weighted periodization commutes with the period integral,
with absolute convergence of the joint subgroup/domain integral. -/
def CompactPeriodPoincareStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) (_hΓ : IsClosed (Γ : Set G))
    [MeasurableSpace Γ] [BorelSpace Γ]
    (μΓ : Measure Γ) [SFinite μΓ] [μΓ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μΓ]
    {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (s : Set X) (_hs : MeasurableSet s) (_hsc : IsCompact (closure s))
    (j : X → G) (_hj : Continuous j) (w : X → ℂ) (_hw : Continuous w)
    (f : C_c(G, ℂ)),
    (∀ g, Integrable
      (fun p : Γ × X => w p.2 * f ((j p.2)⁻¹ * (p.1.val * g)))
      (μΓ.prod (μ.restrict s))) ∧
    ∀ q : LeftQuotient Γ,
      quotientAverage Γ μΓ (fun g => ∫ x in s, w x * f ((j x)⁻¹ * g) ∂μ) q =
        ∫ x in s, w x * quotientAverage Γ μΓ (fun g => f ((j x)⁻¹ * g)) q ∂μ

end Langlands.QuotientIntegration
