import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Real averaging prerequisites for quotient integration

These propositions isolate positive lifting and the kernel calculation used
in the construction of a compatible quotient measure. They assert no proofs.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped CompactlySupported

universe u

/-- A nonnegative compactly supported function whose fiber integral is one on
an arbitrary compact subset of the left quotient. -/
def RealQuotientCompactNormalization : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (H : Subgroup G),
    IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H] (μH : Measure H)
      [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      (K : Set (LeftQuotient H)),
      IsCompact K → ∃ f : C_c(G, ℝ),
        (∀ x, 0 ≤ f x) ∧
        ∀ g : G, Quotient.mk (QuotientGroup.rightRel H) g ∈ K →
          (∫ h : H, f (h.val * g) ∂μH) = 1

/-- Every real compactly supported continuous quotient function has a lift
under actual fiber integration, with a nonnegative lift when it is nonnegative. -/
def RealQuotientPositiveLifting : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (H : Subgroup G),
    IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H] (μH : Measure H)
      [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      (φ : C_c(LeftQuotient H, ℝ)),
      ∃ f : C_c(G, ℝ),
        (∀ g : G, (∫ h : H, f (h.val * g) ∂μH) =
          φ (Quotient.mk (QuotientGroup.rightRel H) g)) ∧
        ((∀ q, 0 ≤ φ q) → ∀ x, 0 ≤ f x)

/-- Fiber-averaging-zero real test functions have zero ambient Haar integral
when both supplied Haar measures are also right invariant. -/
def RealAveragingKernelIntegralZero : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G),
    IsClosed (H : Set G) →
    ∀ [MeasurableSpace H] [BorelSpace H] (μG : Measure G) (μH : Measure H)
      [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
      [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
      (f : C_c(G, ℝ)),
      (∀ g : G, (∫ h : H, f (h.val * g) ∂μH) = 0) →
        (∫ g : G, f g ∂μG) = 0

/-- The three real-averaging obligations used to construct the quotient
functional; this is only a conjunction of explicit proposition definitions. -/
def RealQuotientMeasurePrerequisites : Prop :=
  RealQuotientCompactNormalization.{u} ∧ RealQuotientPositiveLifting.{u} ∧
    RealAveragingKernelIntegralZero.{u}

end Langlands.QuotientIntegration
