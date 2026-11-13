# Rank-one type-D spin identification from the classical presentation

Author: Worker 180.

`Langlands.GroupScheme.typeDRankOneSpin_of_classicalTypeDSpinPresentation.{u}`
proves

```text
ClassicalTypeDSpinPresentationStatement.{u} →
  TypeDRankOneSpinStatement.{u}.
```

The first proposition is an explicit, unproved hypothesis. This theorem
does not prove either the general classification or the unconditional
rank-one target.

## Implemented proof

A private helper works over any field, with any actual numbered
type-`D_n` index, `4 ≤ n`, whose only distinguished vertex is numbered
2 in one-based notation and whose star action fixes the nonfork
vertices. It assumes simple connectedness, absolute almost simplicity
and `splitRank G = 1`.

Apply the general presentation statement for this numbering. It gives
an algebra of degree `degree`, a form in `m` variables and a cover,
together with the rank and index comparisons. The rank comparison
gives `quadraticWittIndex q = 1`, using `ENat.natCast_inj` to pass
from the extended-natural split rank to the natural-number Witt index.
The vertex `e.symm 1` is
distinguished and is a nonfork vertex. The distinguished-vertex
formula produces `j` with
`0 < j ≤ 1` and `2 = j * degree`. Thus `j = 1` and `degree = 2`.
Rewriting `degree = 2` in `m * degree = 2 * n` gives `m = n`.
Substitute these two natural
number equalities. The division-algebra dimension becomes 4, the
symmetric-subspace dimension becomes 3, and the form and morphism
have exactly the types in the target. The proof returns the same
nondegeneracy and spin-cover witnesses without modifying them.

The main theorem splits the exact target's index disjunction:

- For `HasRankOneOuterD4Index`, use its supplied numbering. Each
  Galois element acts either identically or by swapping the fork
  tips, numbered 3 and 4. A nonfork vertex has zero-based number
  less than 2, so this swap fixes it. Injectivity of the numbering
  gives the required actual vertex equality.
- For `HasRankOneInnerD5Index`, use its supplied numbering and
  the triviality of the full star action directly.

The helper then supplies each conclusion. Arithmetic uses `omega`;
the concrete dimension formulas reduce numerically after substitution.
There is no field arithmetic, characteristic split, local-field
argument or appeal to a downstream classification or Kneser–Tits
result.

## Provenance and scope

This is an internal specialization of the two imported propositions.
Its mathematical source interpretation is the degree-2, Witt-index-1
case of the classical type-D descriptions documented in
`ClassicalTypeDSpinPresentationStatement.md`. The additional published
target pair remains unchanged. All universes `u` and all
characteristics, including 2, are retained. No axiom or proof hole is
introduced.
