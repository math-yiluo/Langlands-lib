# Counting tuples by the position of their last nonzero entry

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
is finite combinatorics. It imports [`LinearAlgebra`](LinearAlgebra.md). The
definitions are internal auxiliary constructions, with no literature source. All
declarations are in `Langlands.Conductor.SphericalCyclicity`. Let `k` be a type
with a zero and decidable equality. It is a `Fintype` where sums are taken; in
the application it is the residue field.

## The top index

`top c`, for `c : Fin m → k`, is one plus the largest index `i` with `c i ≠ 0`, or `0`
if `c = 0`. It is defined by recursion on `m`, looking at `c (Fin.last m)` and
otherwise at `Fin.init c`.

- `top_zero_length`, `top_succ` and `top_snoc` give the recursion. `top_snoc` says
  `top (Fin.snoc c x)` is `top c` if `x = 0`, and `m + 1` otherwise.
- `top_le_iff`: `top c ≤ t ↔ ∀ i, t ≤ i → c i = 0`, by induction on `m`. Consequences
  are `top_le` (`top c ≤ m`), `eq_zero_of_top_le` (`c i = 0` when `top c ≤ i`), and
  `ne_zero_of_top_eq` (`c i ≠ 0` when `top c = i + 1`).

## Sums

Write `q = Fintype.card k`. Let `R` be a commutative ring and `φ : ℕ → R`.

- `sum_top_succ`:
  `Σ_{c : Fin (m+1) → k} φ(top c) = Σ_{c : Fin m → k} φ(top c) + (q - 1) q^m φ(m + 1)`.
  The proof reindexes through `Fin.snocEquiv` and splits off the last entry `x`. For
  `x = 0` the top is unchanged. For each of the `q - 1` nonzero `x`, the top is
  `m + 1` for all `q^m` tuples `c`.
- `sum_max_top`: for `J ≤ m`,

  ```
  q · Σ_{c : Fin m → k} φ(max J (top c)) = q^(J+1) φ(J) + Σ_{J < i ≤ m} (q - 1) q^i φ(i).
  ```

  The proof is by induction from `m = J` (`Nat.le_induction`). In the base case every
  tuple has `top c ≤ J`, so the left side is `q · q^J φ(J)` and no geometric sum is
  needed. The inductive step is `sum_top_succ` applied to `t ↦ φ(max J t)`.

## Comparison with the cell matrix

- `cellMatrix_mulVec_row`: for `z j ≠ 0` and `q ≠ 0`,
  `z_j q^(j+1) (cellMatrix *ᵥ a)_j = q^(j+1) a_j + Σ_{i > j} (q - 1) q^i a_i`.
- `cellIndex j c = max j (top c)`, as an element of `Fin (n + 2)`, for
  `j : Fin (n + 2)` and `c : Fin (n + 1) → k`. `cellIndex_val` gives its value.
- `sum_cellIndex`: if `Fintype.card k = q` and all `z i ≠ 0`, then

  ```
  Σ_{c : Fin (n+1) → k} a(cellIndex j c) = z_j q^j (cellMatrix (n + 2) q z *ᵥ a)_j.
  ```

  Extend `a` by zero to `ℕ`, multiply both sides by `q`, and compare `sum_max_top`
  (with `J = j`, `m = n + 1`) with `cellMatrix_mulVec_row`.
