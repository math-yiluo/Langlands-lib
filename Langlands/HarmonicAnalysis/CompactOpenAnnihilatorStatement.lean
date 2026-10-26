import Langlands.HarmonicAnalysis.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-! Compactness of compact-open annihilators under scalar Fourier self-duality. -/

namespace Langlands.HarmonicAnalysis

universe u

/-- An internal prerequisite to scalar Fourier closure, with the original generic
hypotheses. This proposition states the compactness obligation without proving it. -/
def CompactOpenAnnihilatorStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
    [TotallyDisconnectedSpace F]
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F),
    IsSelfDual ψ μ →
      ∀ H : OpenAddSubgroup F, IsCompact (H : Set F) →
        IsCompact {y : F | ∀ x : F, x ∈ H → ψ.complex (x * y) = 1}

end Langlands.HarmonicAnalysis
