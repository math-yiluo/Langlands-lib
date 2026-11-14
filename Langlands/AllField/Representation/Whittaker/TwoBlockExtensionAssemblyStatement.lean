import Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyStatement
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityStatement
import Langlands.AllField.Representation.Whittaker.TwoBlockExtensionStatement
/-! # Conditional assembly of the JPSS two-block extension -/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockExtensionAssemblyStatement TwoBlockWhittakerExtensionStatement
open Langlands.AllField.Whittaker

open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement
open Langlands.AllField.HarmonicAnalysis

universe uF uV₁ uV₂

/-- Row Fourier surjectivity for the canonical topology supplies the remaining
analytic premise for the unchanged, universe-polymorphic extension target. -/
def TwoBlockExtensionAssemblyStatement : Prop :=
  (∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (d : ℕ),
    PadicRowFourierSurjectivityStatement F (⟨⟩ : LocalFieldData F) d) →
  TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂}

end Langlands.AllField.Whittaker
