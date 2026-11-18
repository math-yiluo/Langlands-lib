import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof
import Langlands.Global.RankinSelberg.ComplexPlaceMinusOneProof
import Langlands.Global.RankinSelberg.ComplexPlaceContragredientReduction
import Langlands.Global.RankinSelberg.ComplexStandardPairingParameterProof
import Langlands.Global.RankinSelberg.ComplexPlaceParameterIrreducibleProof

/-! # Reduction of the complex-place functional equation to the local functional equations

`ComplexPlaceFunctionalEquationLocalFEReductionStatement` says that
`ComplexPlaceFunctionalEquationStatement` follows from the two local functional equations at a
complex place, `ComplexLocalUnequalFunctionalEquationStatement` and
`ComplexLocalEqualFunctionalEquationStatement`. The proof combines
`complexPlaceFunctionalEquationLocalReduction`, `complexPlaceMinusOne`,
`complexPlaceContragredientParameterReduction`, `complexPlaceParameterIrreducible` and
`complexStandardPairingParameter`. See the paired Markdown.
-/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **The reduction to the local functional equations.** `ComplexPlaceFunctionalEquationStatement`
follows from the local functional equations at a complex place for unequal and for equal
ranks. -/
def ComplexPlaceFunctionalEquationLocalFEReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement →
    ComplexPlaceFunctionalEquationStatement.{u}

/-- The local reduction, with the minus-one premise proved and the contragredient premise
proved from the irreducibility and local pairing premises, both proved. -/
theorem complexPlaceFunctionalEquationLocalFEReduction :
    ComplexPlaceFunctionalEquationLocalFEReductionStatement.{u} :=
  fun hU hE =>
    complexPlaceFunctionalEquationLocalReduction hU hE complexPlaceMinusOne
      (complexPlaceContragredientParameterReduction complexPlaceParameterIrreducible
        complexStandardPairingParameter)

end Langlands.Global.RankinSelbergGlobal
