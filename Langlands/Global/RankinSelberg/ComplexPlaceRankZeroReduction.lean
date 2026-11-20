import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZeroReduction
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationLocalFEReduction
import Langlands.LocalFactor.Archimedean.ComplexTateProof

/-! # The complex-place functional equation with the rank-one equal-rank case proved

`ComplexPlaceFunctionalEquationStatement` follows from

* the unequal-rank local statement `ComplexLocalUnequalFunctionalEquationStatement`, and
* the equal-rank local statement `ComplexLocalEqualAtRankStatement r` at every positive rank
  index `r`.

The rank-one case (`r = 0`) of the equal-rank local statement is
`complexLocalEqualAtRankStatement_zero` applied to the complex Tate theorem
`ComplexTate.complexArchimedeanTateStatement`. The proof composes
`complexLocalEqualRankZeroReductionStatement` with the Library's
`complexPlaceFunctionalEquationLocalFEReduction`. See the paired Markdown.
-/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **Reduction with the rank-one equal-rank case proved.** The complex-place functional
equation follows from the unequal-rank local statement and the equal-rank local statement at
every positive rank index. -/
def ComplexPlaceRankZeroReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    (∀ r : ℕ, 0 < r → ComplexLocalEqualAtRankStatement r) →
    ComplexPlaceFunctionalEquationStatement.{u}

/-- Proof of `ComplexPlaceRankZeroReductionStatement`. The equal-rank local statement comes
from `complexLocalEqualRankZeroReductionStatement` and the complex Tate theorem; the rest is
`complexPlaceFunctionalEquationLocalFEReduction`. -/
theorem complexPlaceRankZeroReduction : ComplexPlaceRankZeroReductionStatement.{u} :=
  fun hU hpos =>
    complexPlaceFunctionalEquationLocalFEReduction hU
      (complexLocalEqualRankZeroReductionStatement
        Langlands.LocalFactor.ComplexTate.complexArchimedeanTateStatement hpos)

end Langlands.Global.RankinSelbergGlobal
