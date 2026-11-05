import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Algebra.Group.Pointwise

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory Set
open scoped CompactlySupported Pointwise

universe uG uX

/-- The compact test function obtained by weighted integration of translates over
a measurable relatively compact domain, including absolute convergence and support. -/
def CompactPeriodTestStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [FirstCountableTopology G]
    {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (s : Set X) (_hs : MeasurableSet s) (_hsc : IsCompact (closure s))
    (j : X → G) (_hj : Continuous j) (w : X → ℂ) (_hw : Continuous w)
    (f : C_c(G, ℂ)),
    (∀ g, Integrable (fun x => w x * f ((j x)⁻¹ * g)) (μ.restrict s)) ∧
    ∃ k : C_c(G, ℂ),
      (∀ g, k g = ∫ x in s, w x * f ((j x)⁻¹ * g) ∂μ) ∧
      tsupport k ⊆ (j '' closure s) * tsupport f

end Langlands.QuotientIntegration
