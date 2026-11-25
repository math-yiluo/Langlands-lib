import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationLocalFEReduction
import Langlands.Global.RankinSelberg.ComplexPlaceUnequalFunctionalEquationProof
import Langlands.Global.RankinSelberg.ComplexPlaceEqualFunctionalEquationProof

/-!
# The archimedean Rankin–Selberg functional equation at the complex places

A proof of `Langlands.Global.RankinSelbergGlobal.ComplexPlaceFunctionalEquationStatement`: the
Library's reduction `complexPlaceFunctionalEquationLocalFEReduction` applied to the local
functional equations at a complex place for unequal ranks
(`complexLocalUnequalFunctionalEquation`) and for equal ranks
(`complexLocalEqualFunctionalEquation`). See the paired Markdown.
-/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **Jacquet 2009, Theorem 2.1 (i)–(iii), at the complex places, both ranks.** The unequal-rank
and the equal-rank archimedean Rankin–Selberg functional equations hold at every complex place
for actual cuspidal realizations over a number field. -/
theorem complexPlaceFunctionalEquation : ComplexPlaceFunctionalEquationStatement.{u} :=
  complexPlaceFunctionalEquationLocalFEReduction complexLocalUnequalFunctionalEquation
    complexLocalEqualFunctionalEquation

end Langlands.Global.RankinSelbergGlobal
