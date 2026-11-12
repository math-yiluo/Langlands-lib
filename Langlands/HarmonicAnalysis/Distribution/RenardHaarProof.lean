import Langlands.HarmonicAnalysis.Distribution.RenardHaarLeftProof
import Langlands.HarmonicAnalysis.Distribution.RenardHaarConsequencesProof

/-! # Renard II.3.6: Haar distributions and density embeddings -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution.RenardHaar

universe u

/-- The five exact assertions of Renard II.3.6 at the full group universe. -/
theorem statements : Statements.{u} :=
  ⟨leftHaar, rightHaar_of_leftHaar leftHaar,
    positiveScalarUniqueness_of_leftHaar leftHaar,
    measureHaarBridge, densityEmbedding⟩

end Langlands.HarmonicAnalysis.Distribution.RenardHaar
