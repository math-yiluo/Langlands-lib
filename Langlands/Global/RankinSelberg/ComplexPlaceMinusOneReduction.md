# The complex-place reduction without the minus-one premise

Lean module: `Langlands.Global.RankinSelberg.ComplexPlaceMinusOneReduction` (namespace
`Langlands.Global.RankinSelbergGlobal`; universe `u` for the number field).

## Statement

```
def ComplexPlaceFunctionalEquationMinusOneFreeReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement → ComplexPlaceWhittakerModelStatement.{u} →
    ComplexPlaceContragredientParameterStatement.{u} →
    ComplexPlaceFunctionalEquationStatement.{u}
```

`ComplexPlaceFunctionalEquationStatement` (Library module
`Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement`) is the target of the
host task. It is the conjunction of the unequal-rank and the equal-rank functional equations of
Jacquet 2009, Theorem 2.1 (iii), p.6, at one complex place of a number field, for the
archimedean restrictions of global Whittaker functions of actual cuspidal realizations.

The four premises are those of the published reduction
`ComplexPlaceFunctionalEquationReductionStatement` (Library module
`Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction`), with its minus-one
premise `ComplexPlaceMinusOneStatement` removed:

* `ComplexLocalUnequalFunctionalEquationStatement` and
  `ComplexLocalEqualFunctionalEquationStatement`: the two local functional equations for the
  Whittaker models of complex standard modules;
* `ComplexPlaceWhittakerModelStatement`: the bridge premise, that the archimedean restrictions
  of global Whittaker functions lie in the local Whittaker model of the parameter;
* `ComplexPlaceContragredientParameterStatement`: the parameter of a contragredient realization
  at a complex place is a permutation of the inverse characters.

None of these four premises is proved here. The statement is weaker than the target, since it
keeps four open premises, and stronger than the published reduction, since it drops one.

## Proof

`complexPlaceFunctionalEquationMinusOneFreeReduction` applies the published theorem
`complexPlaceFunctionalEquationReduction` to the four premises and to
`complexPlaceMinusOne : ComplexPlaceMinusOneStatement`.

`complexPlaceMinusOne` is proved in `Langlands.Global.RankinSelberg.ComplexPlaceMinusOneProof`,
with helper module `Langlands.Global.RankinSelberg.ComplexPlaceMinusOneScalar`; both modules are
part of this contribution and have their own Markdown. In short: if an actual cuspidal
realization `T` of `GL_(r+1)` has the parameter `d` at the complex place `w`, then `-1 ∈ U(r+1)`
at `w` acts on `T` by `∏_j χ_j(-1)`. The reason is that `-1` at `w` is central, so its
eigenspaces in `T` are subrepresentations. On the complex principal series of `d`, right
translation by `-1` is multiplication by `∏_j χ_j(-1)`. The parameter map sends a nonzero
`U(r+1)`-finite function of the principal series to a nonzero eigenvector of `-1` with this
eigenvalue, and irreducibility of `T` makes that eigenspace all of `T`.

This is the scalar `ω_(π_(σ,u))(-1)` in Jacquet's functional equations: the central character of
the induced representation at `-1`.

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement is internal. It is the published conditional reduction with one premise
discharged, and serves as an intermediate result toward the target.
