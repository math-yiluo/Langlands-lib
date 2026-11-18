import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof
import Langlands.Global.RankinSelberg.ComplexPlaceMinusOneProof
import Langlands.Global.RankinSelberg.ComplexPlaceContragredientReduction

/-! # The combined complex-place reduction

This module combines three Library results about `ComplexPlaceFunctionalEquationStatement`:

* `complexPlaceFunctionalEquationLocalReduction`: the target follows from the two local
  functional equations, the minus-one premise and the contragredient premise;
* `complexPlaceMinusOne`: the minus-one premise holds;
* `complexPlaceContragredientParameterReduction`: the contragredient premise follows from the
  irreducibility premise `ComplexPlaceParameterIrreducibleStatement` and the local pairing premise
  `ComplexStandardPairingParameterStatement`.

The result, `ComplexPlaceFunctionalEquationCombinedReductionStatement`, has four open premises.
See the paired Markdown.
-/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **The combined reduction.** `ComplexPlaceFunctionalEquationStatement` follows from the two
local functional equations, the irreducibility premise for standard modules of cuspidal
parameters and the local pairing premise. -/
def ComplexPlaceFunctionalEquationCombinedReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement →
    ComplexPlaceParameterIrreducibleStatement.{u} → ComplexStandardPairingParameterStatement →
    ComplexPlaceFunctionalEquationStatement.{u}

/-- The local reduction with the minus-one premise proved and the contragredient premise
reduced to the irreducibility and local pairing premises. -/
theorem complexPlaceFunctionalEquationCombinedReduction :
    ComplexPlaceFunctionalEquationCombinedReductionStatement.{u} :=
  fun hU hE hIrr hPair =>
    complexPlaceFunctionalEquationLocalReduction hU hE complexPlaceMinusOne
      (complexPlaceContragredientParameterReduction hIrr hPair)

end Langlands.Global.RankinSelbergGlobal
