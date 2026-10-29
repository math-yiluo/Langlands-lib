# Lower-left rank characterization of actual upper Bruhat cells

Author: Worker 957.

`Langlands.GeneralLinear.UpperBruhatRankCharacterizationStatement.{u}` is a
closed, transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperBruhatRankStatement`. This module states the
proposition only; it provides no proof of it. The proof is a separate
obligation.

The module imports `Langlands.Group.GL.UpperBruhatCells` and
`Mathlib.LinearAlgebra.Matrix.Rank` unchanged and introduces no other
declaration.

## Exact proposition

```text
∀ (K : Type u) [Field K] (n : ℕ) (w : Equiv.Perm (Fin n))
  (g : Langlands.GeneralLinear n K),
  g ∈ upperBruhatCell n K w ↔
    ∀ i j : Fin (n + 1),
      Matrix.rank
          ((fun r c => if i.val ≤ r.val ∧ c.val < j.val then g r c else 0 :
            Matrix (Fin n) (Fin n) K)) =
        Matrix.rank
          ((fun r c =>
              if i.val ≤ r.val ∧ c.val < j.val then permutation n K w r c else 0 :
            Matrix (Fin n) (Fin n) K))
```

The only outer parameter is the universe level `u`. Inside the proposition it
ranges over every type `K : Type u` with every `Field K` instance, with no
restriction on characteristic, cardinality or topology. It ranges over every
natural rank `n`, including `n = 0`, every permutation `w` of `Fin n`, and
every invertible matrix `g` in the existing group
`Langlands.GeneralLinear n K`, Mathlib's units of the matrix ring
`Matrix (Fin n) (Fin n) K`. For each such data it asserts a biconditional:
`g` lies in the actual cell of `w` if and only if the two displayed ranks agree
for every pair `i j : Fin (n + 1)`. The conjunction over `i` and `j` is the
universal quantifier on the right of `↔`; both directions are asserted. No
topology, closure, orbit, rank-characterization or factorization hypothesis
is assumed.

## Padded lower-left corners

For `i j : Fin (n + 1)` the two matrices are square matrices indexed by
`Fin n × Fin n`. Entry `(r, c)` equals the corresponding entry of `g`
(respectively of the permutation matrix) when `i.val ≤ r.val` and
`c.val < j.val`, and equals `0` otherwise. Thus the rows kept are those with
zero-based index at least `i`, the columns kept are those with zero-based index
strictly less than `j`, and everything else is padded by zeros, so all corners
live in the one type `Matrix (Fin n) (Fin n) K`. In particular:

- `i = n` (that is, `i.val = n`, which `Fin (n + 1)` allows) keeps no row,
  and `j = 0` keeps no column; in either case both matrices are zero.
- `i = 0` together with `j = n` keeps every entry, so the two matrices are
  the underlying matrices of `g` and of `permutation n K w` themselves.
- For `n = 0`, `Fin 1` has only `i = j = 0`, and both matrices are the empty
  `0 × 0` matrix.

Zero padding does not change the dimension of the column space, so the rank
of a padded corner is the rank of the actual `(n - i) × j` lower-left
submatrix. This remark explains the meaning only; the module states the
padded form and proves nothing about it.

`Matrix.rank` is Mathlib's definition from `Mathlib.LinearAlgebra.Matrix.Rank`:
`A.rank = finrank K (LinearMap.range A.mulVecLin)`, the dimension of the column
space. In Lean the two corners are written inline as lambda expressions
ascribed the type `Matrix (Fin n) (Fin n) K`; no auxiliary corner definition
is introduced. The decidability of the conditions is the standard one for
`≤` and `<` on `ℕ`.

## Matrix and cell conventions

The first argument of a matrix entry is its row and the second its column.
`g r c` is the entry of the underlying matrix `(g : Matrix (Fin n) (Fin n) K)`,
obtained through the coercion `Units.val`; likewise
`permutation n K w r c` is an entry of the underlying matrix of the existing
permutation unit. By `permutation_entry` in `Langlands.Group.GL.Maps`, that
entry is `if w c = r then 1 else 0`, so the matrix sends the standard basis
vector `e_c` to `e_(w c)`. The permutation is neither inverted nor reversed in
the statement.

`upperBruhatCell n K w`, imported unchanged from
`Langlands.Group.GL.UpperBruhatCells`, is the actual subset

```text
{g | ∃ b₁ ∈ upperTriangularSubgroup n K,
       ∃ b₂ ∈ upperTriangularSubgroup n K, g = b₁ * permutation n K w * b₂}
```

of `Langlands.GeneralLinear n K`, where `upperTriangularSubgroup n K` consists
of the invertible matrices whose entries `(r, c)` with `c < r` vanish; their
diagonal entries are not required to equal one. Hence the cell is `B * p * B`
for the upper triangular subgroup `B` and the permutation matrix `p` of `w`.

For orientation only: the permutation corner for `(i, j)` has a single entry
`1` in each kept column `c` with `i.val ≤ (w c).val` and zeros elsewhere, so
its rank is the number of `c` with `c.val < j.val` and `i.val ≤ (w c).val`.
The statement does not use or prove this count.

## Internal provenance

The proposition is an internal algebraic interface chosen by the project. It
serves the rank route indicated in the published
`Langlands.GeneralLinear.UpperBruhatLocalClosednessStatement`
(`Langlands.Group.GL.UpperBruhatLocalClosednessStatement`), whose Markdown
records that ranks of lower-left submatrices are constant on a cell and that
rank bounds are minor (non)vanishing conditions. That statement concerns
Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974),
Lemma 1.7. The present arbitrary-field formulation is not a claim that Shalika
states or proves it; no external literature theorem is cited for it. It is the
algebraic prerequisite split from the later topological assembly of local
closedness.

A possible later proof, suggested but not implemented or assumed here, uses
the published `Langlands.GeneralLinear.fieldUpperBruhatFactorizationTheorem`
(`Langlands.Group.GL.UpperBruhatProof`) to write `g = a * p' * b` for some
permutation matrix `p'`. Multiplication by invertible upper triangular
matrices preserves every padded lower-left corner rank, and a permutation's
corner-rank profile determines the permutation by finite differences. The
proof may follow any other genuine argument.

## What is not asserted

The module asserts nothing about topology, closures, local closedness, orbits,
dimensions or coordinates of cells. It does not restate the Bruhat
factorization, the disjointness of distinct cells, or uniqueness of `w`, and it
does not assert the orientation count above. It is a statement only, and
remains unproved here.
