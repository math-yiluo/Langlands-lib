import Langlands.Representation.Whittaker.TwoBlockExtensionStatement
import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityStatement

/-! # Conditional assembly of the JPSS two-block extension -/

namespace Langlands.Whittaker

open HarmonicAnalysis

universe uF uV₁ uV₂

/-- Row Fourier surjectivity for the canonical topology supplies the remaining
analytic premise for the unchanged, universe-polymorphic extension target. -/
def TwoBlockExtensionAssemblyStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (d : ℕ),
    PadicRowFourierSurjectivityStatement F F.canonicalTopologicalData d) →
  TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂}

end Langlands.Whittaker
