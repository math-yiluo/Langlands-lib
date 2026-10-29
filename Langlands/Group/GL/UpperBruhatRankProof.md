# Lower-left rank characterization of actual upper Bruhat cells: proof

Author: Worker 957.

`Langlands.GeneralLinear.upperBruhatRankCharacterization.{u}` in
`Langlands.Group.GL.UpperBruhatRankProof` proves the published closed
proposition `Langlands.GeneralLinear.UpperBruhatRankCharacterizationStatement.{u}`
from `Langlands.Group.GL.UpperBruhatRankStatement`, whose type it has exactly.
For every field `K : Type u`, every natural rank `n` (including `0`), every
permutation `w : Equiv.Perm (Fin n)` and every `g : Langlands.GeneralLinear n K`,
it proves both directions of

```text
g ∈ upperBruhatCell n K w ↔
  ∀ i j : Fin (n + 1),
    rank (corner of g at (i, j)) = rank (corner of permutation n K w at (i, j))
```

where the corner at `(i, j)` keeps the entries in rows `r` with `i.val ≤ r.val`
and columns `c` with `c.val < j.val` and replaces every other entry by `0`.
No topology, factorization, closure, orbit or uniqueness hypothesis is added;
the published factorization theorem is used as a proved theorem. The only
axioms reported by the declaration inspection are `propext`,
`Classical.choice` and `Quot.sound`.

The module imports the statement module and
`Langlands.Group.GL.UpperBruhatProof` unchanged.

## Supporting declarations

All helpers are in the namespace `Langlands.GeneralLinear.UpperBruhatRank`,
for a field `K : Type u` and a natural `n`.

- `corner i j M` is the zero-padded corner of a matrix
  `M : Matrix (Fin n) (Fin n) K`, written exactly like the lambda in the
  statement. The main proof uses `change` to restate the target with
  `corner i j (g : Matrix (Fin n) (Fin n) K)` and
  `corner i j (permutation n K w : Matrix (Fin n) (Fin n) K)`; this is a
  definitional restatement of the same proposition.
- `rowMask i` and `colMask j` are the diagonal `0/1` matrices with diagonal
  entries `if i.val ≤ r.val then 1 else 0` and `if c.val < j.val then 1 else 0`.
  `corner_eq_mul` proves `corner i j M = rowMask i * M * colMask j` entrywise
  with Mathlib's `Matrix.diagonal_mul` and `Matrix.mul_diagonal`.
- `count w i k` is the cardinality of the finite set of columns `c : Fin n`
  with `c.val < k` and `i.val ≤ (w c).val`.

## Rank invariance under the upper triangular subgroup

Let `b` be a matrix whose entries `b r s` vanish for `s < r`; this is the
entry condition of `mem_upperTriangularSubgroup_iff`.

- `rowMask_mul_triangular` proves `rowMask i * b = rowMask i * b * rowMask i`:
  in a kept row `r` (so `i ≤ r`), every dropped column `s` (so `s < i`)
  satisfies `s < r`, where `b r s = 0`.
- `triangular_mul_colMask` proves `b * colMask j = colMask j * b * colMask j`:
  in a kept column `c` (so `c < j`), every dropped row `s` (so `j ≤ s`)
  satisfies `c < s`, where `b s c = 0`.

Hence `corner i j (b * M) = (rowMask i * b) * corner i j M` and
`corner i j (M * b) = corner i j M * (b * colMask j)`, and Mathlib's
`Matrix.rank_mul_le_right` and `Matrix.rank_mul_le_left` give the inequalities
`rank_corner_triangular_mul_le` and `rank_corner_mul_triangular_le`: the corner
rank does not increase under left or right multiplication by `b`.

For an actual unit `b ∈ upperTriangularSubgroup n K`, the inverse also lies in
the subgroup, so its entries satisfy the same condition. Applying the
inequality to `b⁻¹` and `b * M` (respectively `M * b`) and cancelling
`b⁻¹ * b = 1` gives the reverse inequality. This proves the equalities
`rank_corner_triangular_mul` and `rank_corner_mul_triangular`, and therefore
`rank_corner_triangular_mul_mul`: for `b₁, b₂` in the upper triangular subgroup
and any unit `p`, every corner of `b₁ * p * b₂` has the same rank as the
corresponding corner of `p`.

## Corner ranks of a permutation matrix

`corner_permutation` uses the published entry formula `permutation_entry`
(entry `(r, c)` equals `if w c = r then 1 else 0`) to prove

```text
corner i j (permutation n K w) =
  permutation n K w * diagonal (fun c => if c.val < j.val ∧ i.val ≤ (w c).val then 1 else 0).
```

Both sides vanish off the entries `(w c, c)`, and at `(w c, c)` both equal
`1` exactly when `i.val ≤ (w c).val` and `c.val < j.val`.

`rank_units_mul` shows that left multiplication by an invertible matrix
preserves rank, by `Matrix.rank_mul_le_right` in both directions (the second
time after multiplying by the inverse). With Mathlib's `Matrix.rank_diagonal`
(under `classical` decidability) and `Fintype.card_subtype`,
`rank_corner_permutation` concludes that the rank of the permutation corner at
`(i, j)` equals `count w i j.val`.

## The corner-rank profile determines the permutation

`count_succ` proves, for `c : Fin n`,

```text
count w i (c.val + 1) = count w i c.val + if i.val ≤ (w c).val then 1 else 0,
```

since enlarging the column range from `c.val` to `c.val + 1` adds only the
column `c`, which is counted exactly when `i.val ≤ (w c).val` (the set is
`insert c` of the smaller one in that case and is unchanged otherwise).

`perm_eq_of_count_eq` assumes `count v i j.val = count w i j.val` for all
`i j : Fin (n + 1)`. For each column `c` it takes `j = c.succ` and
`j = c.castSucc`, whose values are `c.val + 1` and `c.val`; subtracting via
`count_succ` gives `i.val ≤ (v c).val ↔ i.val ≤ (w c).val` for every
`i : Fin (n + 1)`. Choosing `i` with value `(w c).val` and then `(v c).val`
gives `(w c).val ≤ (v c).val` and `(v c).val ≤ (w c).val`, so `v c = w c` for
every `c`, and `v = w` by `Equiv.ext`.

## Assembly of the biconditional

- Forward direction: if `g = b₁ * permutation n K w * b₂` with `b₁, b₂` in
  `upperTriangularSubgroup n K`, then `rank_corner_triangular_mul_mul` gives
  the required equality of every corner rank, for all `i j : Fin (n + 1)`.
- Reverse direction: the published theorem
  `Langlands.GeneralLinear.fieldUpperBruhatFactorizationTheorem`
  (`Langlands.Group.GL.UpperBruhatProof`) writes `g = a * permutation n K v * b`
  with `a`, `b` invertible and entrywise upper triangular, hence members of
  `upperTriangularSubgroup n K` by `mem_upperTriangularSubgroup_iff`. By
  `rank_corner_triangular_mul_mul`, the corner ranks of `g` equal those of
  `permutation n K v`; the hypothesis says they equal those of
  `permutation n K w`. By `rank_corner_permutation` both profiles are `count`
  profiles, so `perm_eq_of_count_eq` gives `v = w`, and `a`, `b` witness
  `g ∈ upperBruhatCell n K w`.

The case `n = 0` needs no separate treatment: all matrices are empty, both
directions go through the same argument, and the uniqueness step is vacuous
because `Fin 0` has no columns.

## Provenance and scope

This is an internal algebraic proof of the project's internal interface; no
external literature proof is claimed. The route (triangular invariance of
lower-left corner ranks, the diagonal form of permutation corners, and
recovery of the permutation by successive column differences) is the standard
elementary argument and follows the route suggested in the task context. All
imported Lean/Markdown pairs, including the target statement pair, are
unchanged. The topological local-closedness of the cells is outside this
module.
