# Reduction of the complex-place functional equation to the local functional equations

Module `Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationLocalFEReduction`,
namespace `Langlands.Global.RankinSelbergGlobal`. Worker 5665 wrote it for Task 7399 (prove
`ComplexPlaceFunctionalEquationStatement`, Jacquet 2009, Theorem 2.1, at a complex place).
Provenance: internal.

## The statement

```lean
def ComplexPlaceFunctionalEquationLocalFEReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement →
    ComplexPlaceFunctionalEquationStatement.{u}
```

In words: the Rankin–Selberg functional equation at the complex places
(`ComplexPlaceFunctionalEquationStatement`) follows from the two local functional equations at a
complex place, for unequal ranks (`ComplexLocalUnequalFunctionalEquationStatement`) and for equal
ranks (`ComplexLocalEqualFunctionalEquationStatement`).

Both premises are Library statements in module `ComplexPlaceFunctionalEquationReduction`; their
proof tasks are Tasks 7569 and 7570. This is a conditional result, and the two premises stay
open here.

## The proof

`complexPlaceFunctionalEquationLocalFEReduction` is a single term. It combines three Library
results and two theorems of this candidate:

- `complexPlaceFunctionalEquationLocalReduction` (Library module
  `ComplexPlaceWhittakerAnalyticProof`): the target follows from the two local functional
  equations, the minus-one premise and the contragredient premise;
- `complexPlaceMinusOne` (Library module `ComplexPlaceMinusOneProof`) proves the minus-one
  premise;
- `complexPlaceContragredientParameterReduction` (Library module
  `ComplexPlaceContragredientReduction`): the contragredient premise follows from the
  irreducibility premise `ComplexPlaceParameterIrreducibleStatement` and the local pairing premise
  `ComplexStandardPairingParameterStatement`;
- `complexPlaceParameterIrreducible` (module `ComplexPlaceParameterIrreducibleProof`, in this
  candidate) proves the irreducibility premise;
- `complexStandardPairingParameter` (module `ComplexStandardPairingParameterProof`, in this
  candidate) proves the local pairing premise.

It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Relation to other reductions

The statement has fewer premises than every earlier reduction of the target:
- `ComplexPlaceFunctionalEquationLocalReductionStatement` (Library) has four;
- `ComplexPlaceFunctionalEquationCombinedReductionStatement` (Worker 822's candidate 2509690e)
  has four;
- the withdrawn three-premise candidate e27ecfdb had three.

Only the two local functional equations remain.

## Provenance

Internal: our own conditional reduction of `ComplexPlaceFunctionalEquationStatement`, stated as
an implication and proved in the same module from Library results and the two new proofs.
