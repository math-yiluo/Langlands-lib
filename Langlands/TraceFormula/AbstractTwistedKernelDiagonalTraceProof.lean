import Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceStatement
import Langlands.TraceFormula.TwistedKernelOperator
import Langlands.Analysis.TraceClassKernelDiagonalProof

/-!
# Proof of the trace of `R(f) ∘ I_θ` as the integral of the diagonal of its kernel

`abstractTwistedKernelDiagonalTrace` proves `AbstractTwistedKernelDiagonalTraceStatement`. By
`twistedKernelOperator_ae_eq`, `R(f) ∘ I_θ` is the integral operator on `Γ \ G` with the continuous
kernel `twistedQuotientKernel Γ θ _ f`; when the operator is trace class this kernel is in
`L²(ν × ν)` (`memLp_uncurry_twistedQuotientKernel`). Brislawn's theorem
(`traceClassContinuousKernelDiagonal`) then gives that the diagonal, which is
`twistedKernelDiagonal Γ θ _ f` (`twistedQuotientKernel_self`), is `ν`-integrable and that its
integral is the trace (`integrable_twistedKernelDiagonal_and_operatorTrace_eq`).

Brislawn 1991, Corollary 3.2 (printed p. 237); Getz–Hahn 2024, §18.5 (printed pp. 487–488).
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.Analysis.OperatorIdeals
open scoped CompactlySupported

universe u

/-- **The diagonal of the twisted kernel is integrable and its integral is the trace.** If
`R(f) ∘ I_θ` is trace class on `L²(Γ \ G, ν)`, then `twistedKernelDiagonal Γ θ _ f` is
`ν`-integrable and `tr (R(f) ∘ I_θ) = ∫ q, twistedKernelDiagonal Γ θ _ f q ∂ν`. -/
theorem integrable_twistedKernelDiagonal_and_operatorTrace_eq
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [μG.IsHaarMeasure]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G ≃ₜ* G) (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    (hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν)
    (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
    (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG)
    (hπ : ∀ (g : G) (φ : Lp ℂ 2 ν),
      (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q))
    (f : C_c(G, ℂ))
    (htc : IsTraceClass ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν))) :
    Integrable (twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ)) ν ∧
      operatorTrace ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
          (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
        (twistOperator Γ θ hθΓ ν hθν)) =
        ∫ q, twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f q ∂ν := by
  have hq := leftQuotient_isOpenQuotientMap Γ
  have : ν.Regular := hν.regular
  have : LocallyCompactSpace (LeftQuotient Γ) := leftQuotient_locallyCompactSpace Γ
  have : SecondCountableTopology (LeftQuotient Γ) :=
    TopologicalSpace.Quotient.secondCountableTopology hq.isOpenMap
  have hdiag : (fun q => twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) q q) =
      twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ) :=
    funext fun q => twistedQuotientKernel_self Γ θ _ _ q
  have h := traceClassContinuousKernelDiagonal (LeftQuotient Γ) ν _
    (twistedQuotientKernel Γ θ (fun γ hγ => (hθΓ γ).2 hγ) (f : G → ℂ)) htc
    (memLp_uncurry_twistedQuotientKernel μG Γ ν hν θ hθΓ hθν π hπnorm hπmeas hπ f htc)
    (twistedKernelOperator_ae_eq μG Γ ν hν θ hθΓ hθν π hπnorm hπmeas hπ f)
    (ae_of_all _ fun q => (continuous_uncurry_twistedQuotientKernel Γ θ θ.continuous
      (fun γ hγ => (hθΓ γ).2 hγ) f).continuousAt)
  rw [hdiag] at h
  exact h

/-- **The trace of `R(f) ∘ I_θ` is the integral of the diagonal of its kernel**
(`AbstractTwistedKernelDiagonalTraceStatement`). -/
theorem abstractTwistedKernelDiagonalTrace : AbstractTwistedKernelDiagonalTraceStatement.{u} := by
  intro G _ _ _ _ _ _ _ _ μG _ _ Γ _ _ _ ν hν θ hθΓ _hθμ hθν π hπnorm hπmeas hπ f htc
  exact (integrable_twistedKernelDiagonal_and_operatorTrace_eq μG Γ ν hν θ hθΓ hθν π hπnorm hπmeas
    hπ f htc).2

end Langlands.TraceFormula
