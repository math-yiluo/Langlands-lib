import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.CompactlySupported

noncomputable section

universe u

namespace Langlands.Analysis

open MeasureTheory
open scoped CompactlySupported

/-- Actual compact continuous tests separate locally integrable complex functions. -/
def CompactTestSeparationStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (F : X → ℂ) (_hF : LocallyIntegrable F μ),
    (∀ f : C_c(X, ℂ), Integrable (fun x => star (f x) * F x) μ) ∧
      (F =ᵐ[μ] 0 ↔ ∀ f : C_c(X, ℂ), (∫ x, star (f x) * F x ∂μ) = 0)

end Langlands.Analysis
