import Langlands.HarmonicAnalysis.Basic

/-! Sigma-finiteness as a consequence of intrinsic Fourier self-duality. -/

namespace Langlands.HarmonicAnalysis

universe u

/-- The sigma-finiteness prerequisite extracted from the scalar Fourier closure
statement, under its original generic hypotheses. This definition supplies no proof. -/
def SelfDualSigmaFiniteStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
    [TotallyDisconnectedSpace F]
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F),
    IsSelfDual ψ μ → MeasureTheory.SigmaFinite μ.measure

end Langlands.HarmonicAnalysis
