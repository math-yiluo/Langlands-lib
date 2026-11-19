import Langlands.TraceFormula.TwistedOrbital
import Langlands.Analysis.OperatorTrace
import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The abstract simple twisted trace formula

For a unimodular locally compact group `G`, a discrete subgroup `Γ`, a continuous
automorphism `θ` of `G` preserving `Γ` and the measures, and a compactly supported
continuous `f`, suppose that `R(f) ∘ I_θ` is trace class on `L²(Γ \ G)`, that the
`Γ`-`θ`-conjugacy classes of `Γ` meeting the `G`-`θ`-orbits of the support of `f`
are finitely many, with representatives `r i`, and that each `(Γ ∩ C_{r i}) \ C_{r i}`
has finite volume and each twisted orbital integral converges absolutely. Then

`tr (R(f) ∘ I_θ) = ∑ i, vol((Γ ∩ C_{r i}) \ C_{r i}) · TO_{r i}(f)`.

Getz–Hahn 2024, Corollary 18.5.1 and Theorem 18.2.5; Deligne–Kazhdan–Vignéras 1984,
A.1.c–d for `θ = id`.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.Analysis.OperatorIdeals
open scoped CompactlySupported

universe uG

/-- The abstract simple twisted trace formula: under the hypotheses listed in the module
docstring, the trace of `R(f) ∘ I_θ` on `L²(Γ \ G, ν)` is the finite sum over
representatives `r i` of the relevant `Γ`-`θ`-conjugacy classes of
`vol((Γ ∩ C_{r i}) \ C_{r i}) · TO_{r i}(f)`. -/
def AbstractSimpleTwistedTraceFormulaStatement : Prop :=
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
    ∀ (n : ℕ) (r : Fin n → Γ),
    (∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j) →
    (∀ γ ∈ Γ, (∃ x : G, f (x⁻¹ * γ * θ x) ≠ 0) →
      ∃ i, IsTwistedConjugate Γ θ (r i : G) γ) →
    ∀ [∀ i, MeasurableSpace (LeftQuotient (twistedCentralizer θ (r i : G)))]
      [∀ i, BorelSpace (LeftQuotient (twistedCentralizer θ (r i : G)))]
      [∀ i, MeasurableSpace
        (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G))))]
      [∀ i, BorelSpace
        (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G))))]
      (μC : ∀ i, Measure (twistedCentralizer θ (r i : G)))
      [∀ i, (μC i).IsMulRightInvariant] [∀ i, IsFiniteMeasureOnCompacts (μC i)]
      [∀ i, (μC i).IsOpenPosMeasure]
      (νC : ∀ i, Measure (LeftQuotient (twistedCentralizer θ (r i : G))))
      (νΓC : ∀ i, Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G))))),
    (∀ i, IsCompatible (twistedCentralizer θ (r i : G)) μG (μC i) (νC i)) →
    (∀ i, IsCompatible (Γ.subgroupOf (twistedCentralizer θ (r i : G))) (μC i)
      Measure.count (νΓC i)) →
    (∀ i, νΓC i Set.univ ≠ ⊤) →
    (∀ i, Integrable (twistedOrbitFunction θ (r i : G) f) (νC i)) →
    operatorTrace ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν)) =
      ∑ i, ((νΓC i Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r i : G) (νC i) f

end Langlands.TraceFormula
