import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.CompactlySupported

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set
open scoped CompactlySupported

universe uG uX

/-- Compact-domain periods give continuous quotient L² test forms with genuine
absolute Fubini and the intrinsic right-Haar modular correction. -/
def CompactPeriodL2PairingStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) (_hΓ : IsClosed (Γ : Set G))
    [MeasurableSpace Γ] [BorelSpace Γ]
    (μΓ : Measure Γ) [SFinite μΓ] [μΓ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μΓ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) [IsFiniteMeasureOnCompacts ν]
    (_hν : IsCompatible Γ μ.inv μΓ ν)
    {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μX : Measure X) [IsFiniteMeasureOnCompacts μX]
    (s : Set X) (_hs : MeasurableSet s) (_hsc : IsCompact (closure s))
    (j : X → G) (_hj : Continuous j) (w : X → ℂ) (_hw : Continuous w)
    (f : C_c(G, ℂ)),
    ∃ (v : Lp ℂ 2 ν) (ℓ : Lp ℂ 2 ν →L[ℂ] ℂ),
      (v : LeftQuotient Γ → ℂ) =ᵐ[ν]
        quotientAverage Γ μΓ (fun g => ∫ x in s, w x * f ((j x)⁻¹ * g) ∂μX) ∧
      ∀ φ : Lp ℂ 2 ν,
        Integrable
          (fun p : G × X => star (w p.2) * star (f ((j p.2)⁻¹ * p.1)) *
            φ (leftQuotientMap Γ p.1)) (μ.inv.prod (μX.restrict s)) ∧
        Integrable (fun x => star (w x) * ((modularCharacter (j x) : ℝ) : ℂ) *
          (∫ g, star (f g) * φ (leftQuotientMap Γ (j x * g)) ∂μ.inv)) (μX.restrict s) ∧
        ℓ φ = inner ℂ v φ ∧
        inner ℂ v φ = ∫ x in s, star (w x) * ((modularCharacter (j x) : ℝ) : ℂ) *
          (∫ g, star (f g) * φ (leftQuotientMap Γ (j x * g)) ∂μ.inv) ∂μX

end Langlands.QuotientIntegration
