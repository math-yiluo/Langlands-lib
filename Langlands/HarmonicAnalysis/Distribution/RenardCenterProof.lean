import Langlands.HarmonicAnalysis.Distribution.RenardCenterCriteriaProof
import Langlands.HarmonicAnalysis.Distribution.RenardCenterCentralityProof
import Langlands.HarmonicAnalysis.Distribution.RenardCenterCategoricalProof
import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsProof
import Langlands.HarmonicAnalysis.Distribution.RenardCompletionProof

/-! # Renard II.3.13 Corollary: center of the category and invariant distributions -/

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis.Distribution.RenardCenter

universe uG uM

/-- Renard II.3.13 Corollary, conditional on the II.3.13 Lemma and Theorem. -/
theorem statements_of (hEP : RenardEssentialProducts.Statements.{uG})
    (hCO : RenardCompletion.Statements.{uG}) : Statements.{uG, uM} :=
  ⟨criteria, categoricalCenterStatement_of hEP hCO
    (fun _ _ _ _ _ _ _ _ _ μ _ pr hpr => centrality μ pr hpr)⟩

/-- Renard II.3.13 Corollary: the criteria for conjugation invariance, and the
identification of the categorical center of smooth representations with the
conjugation-invariant essentially compact distributions. -/
theorem statements : Statements.{uG, uM} :=
  statements_of.{uG, uM} RenardEssentialProducts.statements.{uG}
    RenardCompletion.statements.{uG}

end Langlands.HarmonicAnalysis.Distribution.RenardCenter
