import Langlands.Analysis.Local.QuotientComplex
import Langlands.Analysis.Local.QuotientAverageReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory
open scoped CompactlySupported

universe uG

/-- Compact orbital averaging gives an actual quotient `L²` vector and a continuous
test form, with absolute convergence and unfolding against every `L²` vector. -/
def QuotientL2UnfoldingStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (_hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (_hν : IsCompatible H μG μH ν) (f : C_c(G, ℂ)),
    Continuous (quotientAverage H μH f) ∧
    HasCompactSupport (quotientAverage H μH f) ∧
    ∃ (v : Lp ℂ 2 ν) (ℓ : Lp ℂ 2 ν →L[ℂ] ℂ),
      (v : LeftQuotient H → ℂ) =ᵐ[ν] quotientAverage H μH f ∧
      ∀ φ : Lp ℂ 2 ν,
        Integrable (fun g => star (f g) * φ (leftQuotientMap H g)) μG ∧
        ℓ φ = inner ℂ v φ ∧
        inner ℂ v φ = ∫ g, star (f g) * φ (leftQuotientMap H g) ∂μG

end Langlands.QuotientIntegration
