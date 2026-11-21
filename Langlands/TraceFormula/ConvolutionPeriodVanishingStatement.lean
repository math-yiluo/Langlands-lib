import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Convolution period vanishing

This abstract statement isolates the unfolding in the proof of Getz–Hahn,
Lemma 16.4.2 (2024, printed p. 430). For the precise hypotheses and their
relation to the source, see `ConvolutionPeriodVanishingStatement.md`.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration
open scoped CompactlySupported

universe u

/-- Let `Γ` be a discrete subgroup and `N` a closed subgroup of a Hausdorff, locally
compact, second-countable group `G`. Equip `G` and `N` with left and right invariant
Haar measures and the compact quotient `(Γ ∩ N) \ N` with a compatible measure `νN`.
If `f ∈ C_c(G)` has zero integral along every `a N b` and `φ` is left `Γ`-invariant
and locally integrable, then any quotient function `P` representing the right
convolution `n ↦ ∫_G f(g) φ(n x g) dg` is `νN`-integrable and has integral zero,
for every `x ∈ G`. -/
def ConvolutionPeriodVanishingStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    (N : Subgroup G), IsClosed (N : Set G) →
    ∀ (μN : Measure N) [μN.IsHaarMeasure] [μN.IsMulRightInvariant]
      [MeasurableSpace (LeftQuotient (Γ.subgroupOf N))]
      [BorelSpace (LeftQuotient (Γ.subgroupOf N))]
      (νN : Measure (LeftQuotient (Γ.subgroupOf N))),
    IsCompatible (Γ.subgroupOf N) μN Measure.count νN →
    CompactSpace (LeftQuotient (Γ.subgroupOf N)) →
    ∀ f : C_c(G, ℂ), (∀ a b : G, ∫ n : N, f (a * (n : G) * b) ∂μN = 0) →
    ∀ φ : G → ℂ, (∀ γ ∈ Γ, ∀ g : G, φ (γ * g) = φ g) → LocallyIntegrable φ μG →
    ∀ (x : G) (P : LeftQuotient (Γ.subgroupOf N) → ℂ),
      (∀ n : N, P (Quotient.mk _ n) = ∫ g, f g * φ ((n : G) * x * g) ∂μG) →
      Integrable P νN ∧ ∫ q, P q ∂νN = 0

end Langlands.TraceFormula
