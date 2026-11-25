# The irreducibility premise at a complex place

Module `Langlands.Global.RankinSelberg.ComplexPlaceParameterIrreducibleProof`. The main
results are in namespace `Langlands.Global.RankinSelbergGlobal` and the helpers are in
`Langlands.Global.RankinSelbergGlobal.ComplexPlaceIrreducible`. It is a step towards
`ComplexPlaceFunctionalEquationStatement` (Jacquet 2009, Theorem 2.1, at a
complex place). Provenance: internal.

Main theorem:
`complexPlaceParameterIrreducible : ComplexPlaceParameterIrreducibleStatement.{u}`.

## What is proved

`ComplexPlaceParameterIrreducibleStatement` (module `ComplexPlaceContragredientPremises`) says the
following. Let `T` be an actual cuspidal realization of `GL_(r+1)` over a number field `F` with
compact adele quotient. If `T` has the parameter `d` at the complex place `w`
(`HasComplexPlaceParameter`), then the `U(r+1)`-finite complex standard module `X(d)` is
irreducible in the sense of `IsComplexStandardIrreducible`.

The theorem has no premise. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Along the way, `isIrreducibleGKModule_of_parameter` proves the `(𝔤, K)`-module form
`IsIrreducibleGKModule (complexStandardRep (r+1) d) (complexStandardLie (r+1) d)`. This is the
complex-place conjunct of the Library statement
`Automorphic.CuspidalArchimedeanStandardIrreducibleStatement`, which the Library proves as
`Automorphic.cuspidalArchimedeanStandardIrreducible` (module
`CuspidalArchimedeanComponentIrreducibleProof`).

## Proof

- `isIrreducibleGKModule_of_parameter`. Unpack the parameter into the length condition, an
  injective map `A : X(d) → T`, and its two equivariance clauses. Those clauses are exactly
  `IsComplexStandardIntertwining (r+1) κ π d A` for the compact action `κ` and the Lie action
  `π` of `T` at `w`. Then apply `isIrreducibleGKModule_of_embedding` (module
  `Langlands.Automorphic.ComplexPlaceStandardIrreducible`) with:
  - the irreducible place component `W₀` from the Library's
    `CuspidalOperatorRealization.exists_complexPlaceComponent` (module
    `PlaceComponentExistence`);
  - for `hcomm`, the Library's
    `OperatorRealization.IsComplexPlaceCommutantStable.eq_bot_or_eq_top` (module
    `ComplexPlaceStableOperator`) together with `T.irreducible`.
- `isComplexStandardIrreducible_of_parameter` converts the conclusion to
  `IsComplexStandardIrreducible`. Let `W` be stable under right translations
  `complexStandardTranslate` and right derivatives `complexStandardDerivative`. The helpers show
  that `W` is stable under `complexStandardRep` and `complexStandardLie`:
  - `translate_eq_rep`, `derivative_eq_lie`: the identity map is an intertwining map
    (`isComplexStandardIntertwining_id`);
  - `rep_mem`: for a unitary matrix `k`, apply translation stability to
    `⟨Unitary.toUnits k, k.2⟩`;
  - `lie_mem`: induction on tensors. `z ⊗ X = z • (1 ⊗ X)`, and derivative stability handles
    `1 ⊗ X`.
- `complexPlaceParameterIrreducible` applies the previous lemma.

Mathematically, the realization at `w` is a sum of copies of one irreducible module. So `X(d)`,
which embeds into it, is semisimple with all simple summands isomorphic. `X(d)` also contains a
vector that every `U(n)`-equivariant endomorphism scales: the lowest `U(n)`-type vector of
multiplicity one, from the Library's `complexLowestKTypeMultOne` via
`ComplexStandardScalarVector.exists_isScalarVector`. That forces a single summand.

## Implementation notes

- The module declares the same local `AddCommGroup` instances on the Library's function spaces
  as `ComplexPlaceStableOperator`.
- The abstract argument lives in `ComplexPlaceStandardIrreducible`, over a type variable `V`.
  Stating it directly on `T.realization.Space` made typeclass synthesis for the operator algebra
  time out.

## Provenance

Internal. The route is the multiplicity-one argument:
isotypy at `w` plus a `U(n)`-type of multiplicity one. It is carried out from Library results.
For the mathematical background (local components of cuspidal representations are irreducible),
see Getz–Hahn (2024), displays (11.14)–(11.17), as cited in
`Langlands.Automorphic.CuspidalArchimedeanComponentStatement`.
