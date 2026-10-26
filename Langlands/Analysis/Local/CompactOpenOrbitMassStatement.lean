import Langlands.Analysis.Local.QuotientTopology

/-!
# Compact open quotient orbit averaging and mass

This proposition uses the actual supplied Haar and compatible quotient measures.
It states internal consequences of compact-test quotient compatibility.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure

universe uG

/-- The indicator of a compact open subgroup averages to its subgroup-intersection
mass on the identity quotient orbit, whose measure is the corresponding Haar ratio. -/
def CompactOpenOrbitMassStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G), IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H]
      [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
      (μG : Measure G) (μH : Measure H)
      [IsHaarMeasure μG] [μG.Regular]
      [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      (K : OpenSubgroup G), IsCompact (K : Set G) →
      ∀ (ν : Measure (LeftQuotient H)), IsCompatible H μG μH ν →
        let q : G → LeftQuotient H := leftQuotientMap H
        let Ω := q '' (K : Set G)
        let A := {h : H | h.val ∈ K}
        let a : ℝ := (μH A).toReal
        IsCompact Ω ∧ IsOpen Ω ∧
          IsCompact A ∧ IsOpen A ∧
          0 < μH A ∧ μH A < ⊤ ∧
          0 < ν Ω ∧ ν Ω < ⊤ ∧
          (∀ x : LeftQuotient H,
            quotientAverage H μH ((K : Set G).indicator (fun _ => (1 : ℂ))) x =
              (a : ℂ) * Ω.indicator (fun _ => (1 : ℂ)) x) ∧
          ν Ω = μG (K : Set G) / μH A ∧
          (∫ x : LeftQuotient H, Ω.indicator (fun _ => (1 : ℂ)) x ∂ν) =
            (((μG (K : Set G)).toReal / a : ℝ) : ℂ)

end Langlands.QuotientIntegration
