import Langlands.HarmonicAnalysis.RenardHomogeneousQuotientProof
import Langlands.HarmonicAnalysis.RenardHomogeneousAveragingProof

/-! # Renard II.3.9: invariant functionals and homogeneous-space comparisons -/

noncomputable section

namespace Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard

universe uG

/-- The five assertions of Renard II.3.9 at the full group universe. -/
theorem statements : Statements.{uG} :=
  ⟨invariantFunctional, averagingStatement, quotientTest, compactInduction,
    pointwiseModuleSheaf⟩

end Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard
