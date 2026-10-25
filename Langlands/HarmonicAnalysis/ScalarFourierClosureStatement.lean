import Langlands.HarmonicAnalysis.Basic

/-! Scalar Fourier closure and sigma-finiteness as consequences of self-duality. -/

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe u

/-- The scalar prerequisites for finite-product Fourier analysis, stated under
the original generic hypotheses. This proposition does not supply a proof. -/
def ScalarFourierClosureStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
    [TotallyDisconnectedSpace F]
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F),
    IsSelfDual ψ μ →
      SigmaFinite μ.measure ∧
      ∀ f : SchwartzBruhat F, ∃ g : SchwartzBruhat F,
        ∀ y : F, g y = fourierIntegral ψ μ f y

end Langlands.HarmonicAnalysis
