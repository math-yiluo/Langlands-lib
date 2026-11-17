# Exact finite Cartan classification: matrix interface

This internal statement isolates the matrix classification needed by the
published actual-group target
`Langlands.GroupScheme.AbsolutelyAlmostSimpleCartanClassificationStatement`.
It introduces no group-theoretic assumptions or conclusions.

For an integral square matrix `M` indexed by an arbitrary type `ι : Type u`,
`FiniteCartanMatrix.HasCartanMatrix M N` means that an equivalence
`e : ι ≃ Fin n` preserves every ordered entry:
`M i j = N (e i) (e j)`. The equivalence numbers the entire index type.
`FiniteCartanMatrix.HasIrreducibleCartanType M` is the disjunction of these
exact presentations for the following Mathlib matrices:

| Matrix | Rank |
| --- | --- |
| `CartanMatrix.A n` | `1 ≤ n` |
| `CartanMatrix.B n`, `CartanMatrix.C n` | `2 ≤ n` |
| `CartanMatrix.D n` | `4 ≤ n` |
| `CartanMatrix.E 6`, `CartanMatrix.E 7`, `CartanMatrix.E 8` | 6, 7, 8 |
| `CartanMatrix.F₄`, `CartanMatrix.G₂` | 4, 2 |

The orientation of multiple edges is retained. Both rank-two B and C
presentations are allowed; uniqueness is not asserted.

`FiniteCartanClassificationStatement` quantifies over every nonempty finite
type `ι`, with a chosen `Fintype` and decidable equality, and every integral
matrix `M`. It assumes Mathlib's `M.IsFiniteCartan` and
`M.IsIndecomposable`. The former requires diagonal entries 2, nonpositive
off-diagonal entries, symmetric zero entries, and a positive integral
diagonal symmetrizer whose product with `M` is positive definite. The latter
rules out a nontrivial block-triangular decomposition under reindexing.
The conclusion is the exact family predicate above.

The provenance is internal: these predicates extract the finite matrix
enumeration obligation from the published actual Tits-index target without
changing that target. This file states the obligation and does not supply
its proof, the actual-group irreducibility bridge, or a local-field
classification.
