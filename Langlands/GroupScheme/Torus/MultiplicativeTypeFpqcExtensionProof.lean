import Langlands.GroupScheme.Torus.MultiplicativeTypeCoefficientExtension
import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalDeformationProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeFibralCriterionProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionProof

/-! # Fpqc descent and extensions for groups of multiplicative type -/

universe u

namespace Langlands.GroupScheme

/-- Fpqc descent and the extension property for groups of multiplicative type
(Conrad, *Reductive group schemes*, Corollary B.4.2). -/
theorem multiplicativeTypeFpqcExtension :
    MultiplicativeTypeFpqcExtensionStatement.{u} :=
  ExtensionReduction.fpqcExtension_of_threeStatements.{u}
    multiplicativeTypeFibralCriterion
    multiplicativeTypeCompleteLocalDeformation
    multiplicativeTypeFieldExtension

end Langlands.GroupScheme
