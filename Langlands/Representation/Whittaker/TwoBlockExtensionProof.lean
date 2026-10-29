import Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyProof
import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityProof

/-! # The JPSS two-block Whittaker extension formula -/

namespace Langlands.Whittaker

universe uF uV₁ uV₂

/-- Every tail coefficient with a row cutoff extends to an actual coefficient
of the canonical ordered normalized upper two-block induction. -/
theorem twoBlockWhittakerExtension :
    TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂} := by
  apply twoBlockWhittakerExtension_of_rowFourierSurjectivity.{uF, uV₁, uV₂}
  intro p _ F d
  exact HarmonicAnalysis.padicRowFourierSurjectivity F F.canonicalTopologicalData d

end Langlands.Whittaker
