import Langlands.Global.RankinSelberg.ComplexPlaceMinusOneProof

/-! # The complex-place reduction without the minus-one premise

The published reduction `ComplexPlaceFunctionalEquationReductionStatement` derives
`ComplexPlaceFunctionalEquationStatement` from five premises. One of them,
`ComplexPlaceMinusOneStatement`, is proved in
`Langlands.Global.RankinSelberg.ComplexPlaceMinusOneProof` (`complexPlaceMinusOne`). This module
states the resulting reduction with the four remaining premises and proves it. See the paired
Markdown.
-/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **The reduction without the minus-one premise.** `ComplexPlaceFunctionalEquationStatement`
follows from the two local functional equations, the bridge premise
`ComplexPlaceWhittakerModelStatement` and the contragredient premise
`ComplexPlaceContragredientParameterStatement`. -/
def ComplexPlaceFunctionalEquationMinusOneFreeReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement → ComplexPlaceWhittakerModelStatement.{u} →
    ComplexPlaceContragredientParameterStatement.{u} →
    ComplexPlaceFunctionalEquationStatement.{u}

/-- The published reduction with its minus-one premise discharged by `complexPlaceMinusOne`. -/
theorem complexPlaceFunctionalEquationMinusOneFreeReduction :
    ComplexPlaceFunctionalEquationMinusOneFreeReductionStatement.{u} :=
  fun hU hE hmodel hdual =>
    complexPlaceFunctionalEquationReduction hU hE hmodel complexPlaceMinusOne hdual

end Langlands.Global.RankinSelbergGlobal
