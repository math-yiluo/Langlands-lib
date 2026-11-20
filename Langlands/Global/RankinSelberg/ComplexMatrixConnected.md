# The invertible complex matrices form a connected set

Module `Langlands.Global.RankinSelberg.ComplexMatrixConnected`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Statement

`ComplexMatrixUnitsPreconnectedStatement` says that for every `n : ℕ` the set
`{X : Matrix (Fin n) (Fin n) ℂ | IsUnit X}` of invertible `n × n` complex matrices is
preconnected. The topology on `Matrix (Fin n) (Fin n) ℂ` is Mathlib's, the product topology on
the entries. Since a complex square matrix is a unit exactly when its determinant is nonzero,
this set is the underlying set of `GL_n(ℂ)` inside `M_n(ℂ)`.

The module also proves:

- `isPreconnected_complexMatrixUnits n`: the same assertion for a fixed `n`. This is the theorem
  Worker 766 (Task 7570) asked for.
- `isConnected_complexMatrixUnits n`: the set is also connected. It is nonempty because it
  contains the identity matrix.
- `complexMatrixUnitsPreconnected`: the proof of `ComplexMatrixUnitsPreconnectedStatement`.

## Provenance

The statement is internal. It is the standard fact that `GL_n(ℂ)` is connected, and Worker 766
requested it for Task 7570. There it propagates the equality of two functions on `GL_n(ℂ)` with
identical jets at the identity to the whole group. The statement uses no definitions beyond
Mathlib's.

## Proof

Two auxiliary declarations carry the polynomial argument.

- `complexMatrixSegmentDetPoly X Y : ℂ[X]` is `det (X.map C + T • (Y - X).map C)`, with `T` the
  polynomial variable. It is the determinant of the affine line through `X` and `Y`.
- `eval_complexMatrixSegmentDetPoly`: its value at `t : ℂ` is `det (X + t • (Y - X))`. The
  evaluation map `evalRingHom t` commutes with `det` (`RingHom.map_det`), and the evaluated
  matrix is computed entrywise.
- `complexMatrixSegmentDetPoly_ne_zero`: if `X` is invertible, the polynomial is nonzero,
  because its value at `0` is `det X ≠ 0`.

In `isPreconnected_complexMatrixUnits` we apply `isPreconnected_of_forall_pair`, which asks for
a preconnected subset of the invertible matrices containing any two given invertible matrices
`X` and `Y`. Let `p` be the polynomial above. It is nonzero, so its root set `Z` is finite
(`Polynomial.finite_setOfPred_isRoot`), hence countable. Since `ℂ` has real dimension `2 > 1`,
the complement `ℂ \ Z` is path connected (`Set.Countable.isPathConnected_compl_of_one_lt_rank`).
The candidate subset is the image of `ℂ \ Z` under the continuous map `f t = X + t • (Y - X)`.

- The image is preconnected, being the continuous image of a connected set.
- It consists of invertible matrices: for `t ∉ Z`, `det (f t) = p.eval t ≠ 0`, and
  `Matrix.isUnit_iff_isUnit_det` applies.
- It contains `X = f 0` and `Y = f 1`: the points `0` and `1` lie outside `Z` because
  `p.eval 0 = det X` and `p.eval 1 = det Y` are nonzero.

Connectedness then follows from preconnectedness and nonemptiness.
