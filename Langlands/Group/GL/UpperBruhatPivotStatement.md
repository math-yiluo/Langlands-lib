# Ordered pivot isolation for upper Bruhat induction

Authors: Worker 330 (Lean statement and documentation) and Worker 308
(statement interface and parent proof design).

`Langlands.GeneralLinear.FieldUpperBruhatPivotTheorem.{u}` is a closed,
transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperBruhatPivotStatement`. This module states a reduction
proposition and provides no proof of it.

For every field `K : Type u`, every `n : ℕ`, and every invertible matrix
`g : Langlands.GeneralLinear (n + 1) K`, it asks for invertible matrices
`L R : Langlands.GeneralLinear (n + 1) K`, a column `p : Fin (n + 1)`, and
`h : Langlands.GeneralLinear n K` satisfying all five conditions:

1. `L i j = 0` whenever `j < i`.
2. `R i j = 0` whenever `j < i`.
3. `(L * g * R) (Fin.last n) j = if j = p then 1 else 0` for every column `j`.
4. `(L * g * R) i.castSucc p = 0` for every `i : Fin n`.
5. `(L * g * R) i.castSucc (p.succAbove j) = h i j` for every `i j : Fin n`.

The first two conditions mean that both factors are upper triangular; their
diagonal entries are not required to equal one. Their invertibility, and that
of the remaining minor `h`, is part of their actual general linear group type.
The module imports the existing `Langlands.Group.GL.Basic` and
`Langlands.Group.GL.Maps` unchanged. `GeneralLinear` is the existing abbreviation
for Mathlib's units of the matrix ring on `Fin` coordinates.

## Row and column conventions

The first argument of a matrix entry is its row and the second its column.
Multiplication is ordinary matrix multiplication: `L` acts on the left by row
operations and `R` acts on the right by column operations. The product
`L * g * R` is parsed as `(L * g) * R`.

`Fin.last n` is the final row, with zero-based index `n`, while `i.castSucc`
embeds the first `n` rows without changing their indices. The third condition
makes the final row the unit row supported at `p`; the fourth clears the rest
of that pivot column. After deleting the final row and column `p`, the fifth
condition identifies the remaining matrix with the invertible matrix `h`.

The remaining columns are enumerated by the increasing map
`p.succAbove : Fin n → Fin (n + 1)`. It sends `j` to `j.castSucc` when
`j.castSucc < p`, and to `j.succ` otherwise, thereby skipping exactly `p`
and retaining the original order. There is no arbitrary enumeration or
permutation of the remaining columns in this interface.

The field, its instance, the rank, and the input matrix are all quantified
inside the proposition; the only outer parameter is the universe level `u`.
There is no restriction on characteristic and no topology is assumed. The
case `n = 0` is included: `g` is a one-by-one invertible matrix, `p` is the sole
column, and `h` has rank zero. The last two conditions then quantify over the
empty type `Fin 0`, while the final-row condition still normalizes the unique
entry to one. The caller supplies no pivot, reduction certificate, minor
invertibility assumption, or Bruhat factorization hypothesis.

## Internal provenance and intended use

This is an internal algebraic reduction designed by Worker 308 for the
inductive proof of the already published
`Langlands.GeneralLinear.FieldUpperBruhatFactorizationTheorem` in
`Langlands.Group.GL.UpperBruhatStatement`. The interface separates pivot
isolation and invertibility of the ordered remaining minor from the parent's
induction, extension of triangular factors and permutations, and factor
assembly. It does not restate the final Bruhat factorization proposition.

The proposed later proof route chooses the first nonzero entry of the last
row, normalizes it, clears the entries to its right by upper triangular column
operations, clears the entries above it by upper triangular row operations,
and proves the remaining minor invertible. This is only the motivation for
the interface, not an implemented proof or an additional hypothesis. The
statement does not specify how the existential witnesses are chosen and
asserts no uniqueness. Its provenance is the project's proof decomposition;
no external literature theorem is claimed. Proving this reduction and using
it to finish the parent factorization are separate proof obligations.
