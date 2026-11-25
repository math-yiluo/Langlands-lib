import Langlands.TraceFormula.TwistedOrbital
import Langlands.Analysis.OperatorTrace
import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The trace of `R(f) ∘ I_θ` as the integral of the diagonal of its kernel

For a unimodular locally compact group `G`, a discrete subgroup `Γ`, a continuous
automorphism `θ` of `G` preserving `Γ` and the measures, the right regular representation `π`
of `G` on `L²(Γ \ G)` and a compactly supported continuous `f`, the operator
`R(f) ∘ I_θ` (`R(f) φ (x) = ∫ f(g) φ(x g) dg`, `I_θ φ = φ ∘ θ̄⁻¹`) is the integral operator on
`Γ \ G` with kernel `K(x, y) = ∑ γ, f (x⁻¹ γ θ y)` (`twistedKernel Γ θ f`). The statement says
that when `R(f) ∘ I_θ` is trace class, its trace is the integral over `Γ \ G` of the diagonal
`x ↦ K(x, x)` (`twistedKernelDiagonal`).

Getz–Hahn 2024, §18.5 (the kernel `K_f(g, θ(h))` of `R(f) ∘ I_θ` and the trace as the integral
of `K(g, θ(g))`, citing Brislawn 1991, Corollary 3.2, printed p. 237).
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.Analysis.OperatorIdeals
open scoped CompactlySupported

universe uG

/-- The trace of `R(f) ∘ I_θ` on `L²(Γ \ G, ν)` is the integral of the diagonal of the twisted
kernel: for the data and hypotheses of `AbstractSimpleTwistedTraceFormulaStatement` up to and
including the trace-class hypothesis, the trace is
`∫ q, twistedKernelDiagonal Γ θ _ f q ∂ν`. -/
def AbstractTwistedKernelDiagonalTraceStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)), IsCompatible Γ μG Measure.count ν →
    ∀ (θ : G ≃ₜ* G) (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ),
    MeasurePreserving θ μG μG →
    ∀ (hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν)
      (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
      (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
      (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG),
    (∀ (g : G) (φ : Lp ℂ 2 ν),
      (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q)) →
    ∀ f : C_c(G, ℂ),
    IsTraceClass ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν)) →
    operatorTrace ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν)) =
      ∫ q, twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f q ∂ν

end Langlands.TraceFormula
