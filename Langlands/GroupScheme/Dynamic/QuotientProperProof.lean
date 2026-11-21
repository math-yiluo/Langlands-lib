import Langlands.GroupScheme.Dynamic.QuotientProperAffineReduction
import Langlands.GroupScheme.Reductive.LinearQuotientAffineProof

/-! # Properness of supplied dynamic parabolic quotients -/

universe u

namespace Langlands.GroupScheme

/-- The structure morphism of every supplied quotient in the published statement is proper. -/
theorem dynamicQuotientProper : DynamicQuotientProperStatement.{u} :=
  dynamicQuotientProper_of_reductiveLinearQuotientAffine reductiveLinearQuotientAffine

end Langlands.GroupScheme
