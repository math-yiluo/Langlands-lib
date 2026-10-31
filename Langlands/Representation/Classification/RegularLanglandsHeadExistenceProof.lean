import Langlands.Representation.Classification.RegularLanglandsHeadComparisonReduction
import Langlands.Representation.Classification.RelativeRegularComparisonProof

/-! Regular tempered standard modules have strong irreducible heads. -/

namespace Langlands

universe uF uV

/-- Every regular tempered GL standard module has an actual smooth irreducible
head with a kernel shared by every surjective irreducible quotient map. -/
theorem glRegularLanglandsHeadExistence :
    GLRegularLanglandsHeadExistenceStatement.{uF, uV} :=
  glRegularLanglandsHeadExistence_of_relativeRegularComparison.{uF, uV}
    (glRelativeRegularComparison.{uF, max uF uV, max uF uV, max uF uV})

end Langlands
