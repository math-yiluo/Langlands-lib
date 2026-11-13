import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFunctionalEquationProof

/-!
# The unequal-rank JPSS functional equation over every nonarchimedean local field

Jacquet, Piatetski-Shapiro and Shalika 1983, Theorem (2.7)(iii), printed pages
390–391, for unequal ranks over an arbitrary nonarchimedean local field (any
characteristic). The all-field port proves the statement for supplied data
`T : LocalFieldData F`; the reduction module transfers it to the hypothesized
residue cardinality, absolute value, uniformizer and Borel structures of the
published target.
-/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- JPSS 1983, Theorem (2.7)(iii), unequal ranks, over every nonarchimedean
local field. -/
theorem localFieldUnequalRankFunctionalEquation :
    LocalFieldUnequalRankFunctionalEquationStatement.{uF, uV, uW} :=
  Langlands.AllField.RankinSelberg.localFieldUnequalRankFunctionalEquation_of_allField
    fun F _ _ _ _ n r =>
      Langlands.AllField.RankinSelberg.unequalRankFunctionalEquation.{uF, uV, uW} F
        (LocalFieldData.ofInstances F) n r

end Langlands.RankinSelberg
