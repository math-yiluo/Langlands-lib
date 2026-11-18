# The combined complex-place reduction

Lean module: `Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationCombinedReduction`
(namespace `Langlands.Global.RankinSelbergGlobal`; universe `u` for the number field).

## Statement

```
def ComplexPlaceFunctionalEquationCombinedReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement →
    ComplexPlaceParameterIrreducibleStatement.{u} → ComplexStandardPairingParameterStatement →
    ComplexPlaceFunctionalEquationStatement.{u}
```

`ComplexPlaceFunctionalEquationStatement` (Library module
`Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement`) is the target of the
host task. It is the conjunction of the unequal-rank and the equal-rank functional equations of
Jacquet 2009, Theorem 2.1 (iii), p.6, at one complex place of a number field, for the
archimedean restrictions of global Whittaker functions of actual cuspidal realizations.

The four premises are all Library declarations, and none is proved here:

* `ComplexLocalUnequalFunctionalEquationStatement` and
  `ComplexLocalEqualFunctionalEquationStatement` (module
  `Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction`): the two local
  functional equations for the Whittaker models of complex standard modules.
* `ComplexPlaceParameterIrreducibleStatement` (module
  `Langlands.Global.RankinSelberg.ComplexPlaceContragredientPremises`): the `U(r+1)`-finite
  complex standard module of a parameter of an actual cuspidal realization at a complex place is
  an irreducible `(𝔤, K)`-module.
* `ComplexStandardPairingParameterStatement` (same module): if two lists `d`, `dd` of `n` complex
  characters have irreducible `U(n)`-finite standard modules with a nonzero invariant bilinear
  pairing, then `dd` is a permutation of the inverse characters of `d`.

## Proof

`complexPlaceFunctionalEquationCombinedReduction` combines three Library theorems:

1. `complexPlaceFunctionalEquationLocalReduction` (module
   `Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof`) derives the target from
   the two local premises, `ComplexPlaceMinusOneStatement` and
   `ComplexPlaceContragredientParameterStatement`.
2. `complexPlaceMinusOne` (module `Langlands.Global.RankinSelberg.ComplexPlaceMinusOneProof`)
   proves `ComplexPlaceMinusOneStatement`.
3. `complexPlaceContragredientParameterReduction` (module
   `Langlands.Global.RankinSelberg.ComplexPlaceContragredientReduction`) derives
   `ComplexPlaceContragredientParameterStatement` from the irreducibility premise and the local
   pairing premise.

The proof applies (1) to the two local premises, to (2), and to (3) applied to the
irreducibility and pairing premises. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The statement is internal. It is `ComplexPlaceFunctionalEquationLocalReductionStatement` with the
minus-one premise proved and the contragredient premise replaced by the two premises of
`ComplexPlaceContragredientParameterReductionStatement`. It is an intermediate result toward the
target. The Markdown of the three source modules explains why each open premise is expected to
hold.
