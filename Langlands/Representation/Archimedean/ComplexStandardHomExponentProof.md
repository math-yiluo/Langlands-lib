# The exponent shape of intertwinings between complex principal series

Lean module: `Langlands.Representation.Archimedean.ComplexStandardHomExponentProof`.

## Result

`Langlands.Archimedean.complexStandardHomExponent : ComplexStandardHomExponentStatement`.

The statement `ComplexStandardHomExponentStatement` (E) is the Library's, in module
`ComplexStandardHomExponent` (see `ComplexStandardHomExponent.md`). This module does not change
it. In words: let `n : ℕ` and `d c : Fin n → ComplexCharacterData`. Let `T` be a nonzero
`ℂ`-linear map from the `U(n)`-finite functions of `complexStandardModule n (List.ofFn d)` to
those of `complexStandardModule n (List.ofFn c)`, and suppose `T` is a `(𝔤, K)`-module map
(`IsComplexStandardIntertwining`). Then there are a permutation `σ` of `Fin n` and
`u v : Fin n → ℤ`, both nonnegative integer combinations of the simple roots
(`IsNonnegSimpleRootCombination`), such that for every `j`

* `(c j).exponent = (d (σ j)).exponent + (u j + v j) / 2`, and
* `(c j).weight = (d (σ j)).weight + (u j - v j)`.

The theorem has no hypotheses beyond those of the statement. It uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof is one line. It applies the Library's reduction theorem to the Library's proof of JE:

```
complexStandardHomExponentJacquetReduction complexStandardJacquetExponent
```

* `complexStandardHomExponentJacquetReduction : ComplexStandardHomExponentJacquetReductionStatement`
  (module `ComplexStandardHomExponentJacquetReduction`) proves
  `ComplexStandardJacquetExponentStatement → ComplexStandardHomExponentStatement`.
  For a nonzero intertwining `T : X(d) → X(c)`, the functional `ℓ(f) = (T f)(1)` is nonzero.
  It is a Jacquet functional on `X(d)` whose exponents are those of `c`:
  `a_j = 2 t(c_j) + (n - 1) - 2j` and `b_j = i l(c_j)`. JE gives `σ`, `u`, `v` with
  `a_j = 2 t(d_{σ j}) + (n - 1) - 2j + (u_j + v_j)` and `b_j = i (l(d_{σ j}) + u_j - v_j)`.
  Comparing the two formulas gives E with the same `σ`, `u`, `v`.
* `complexStandardJacquetExponent : ComplexStandardJacquetExponentStatement`
  (module `ComplexStandardJacquetExponentProof`) proves JE. It applies the route theorem
  `complexStandardJacquetExponentRoute` to the Casselman–Osborne, translation and
  antidominant-bound results. See that module's Markdown.

The module imports exactly these two modules.

## Provenance

This is an internal proof of the Library statement E. E is stated in `ComplexStandardHomExponent`
as a step of the proof of `ComplexLanglandsQuotientUniqueStatement`. The JE → E reduction is
`ComplexStandardHomExponentJacquetReduction`. JE is proved in `ComplexStandardJacquetExponentProof`.
