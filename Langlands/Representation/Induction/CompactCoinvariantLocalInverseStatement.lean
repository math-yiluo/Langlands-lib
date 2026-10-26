import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Analysis.Local.QuotientMass
import Mathlib.RepresentationTheory.Coinvariants

/-! Local characterization of a proposed normalized map on inducing coinvariants. -/

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure

universe uG uV

/-- Existence of a complex linear map on inducing coinvariants with the normalized
double-coset-section value for every admissible compact open subgroup.
This is a closed statement with independent group and coefficient universes. -/
def CompactCoinvariantLocalInverseExists : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G],
    (∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H]
      (μG : Measure G) (μH : Measure H)
      [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
      [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
      [BorelSpace (QuotientIntegration.LeftQuotient H)]
      (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
      (hν : QuotientIntegration.IsCompatible H μG μH ν)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ H V),
      IsSmooth σ →
        ∃ T : Representation.Coinvariants σ →ₗ[ℂ]
            Representation.Coinvariants (compactInduced H σ),
          ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
            (hv : v ∈ fixedVectors σ (conjOpenSubgroup H K 1).toSubgroup),
            T (Representation.Coinvariants.mk σ v) =
              (Complex.ofReal ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal))⁻¹ •
                Representation.Coinvariants.mk (compactInduced H σ)
                  (compactDoubleCosetSection H σ K hK 1 v hv)

end Langlands.Induction
