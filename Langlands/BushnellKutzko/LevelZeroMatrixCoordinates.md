# The adapted basis in standard coordinates of `F^n`

For a chain `L` in `F^n` with layer bases `b`, the columns of `basisMat` are
the adapted basis vectors and `basisMatInv` is its inverse.
[Adapted basis](LevelZeroAdaptedBasis.md)

- `stdToGL` applies `stdToAut` and then the inverse of
  `Matrix.GeneralLinearGroup.toLin`. On matrices, `stdToGL x` is
  `basisMat * x * basisMatInv`. It is a topological group isomorphism by
  continuity of matrix multiplication and `Units.continuous_iff`.
- When `e f = n`, `blockEquiv hn` sends `(a, i)` to `a + f i`, so the first
  block becomes the first `f` coordinates. The matrix `changeGL` has the
  adapted basis columns in this order.
- `changeGL_conj` and `stdToGL_reindex_symm` identify `stdToGL` applied to
  a reindexed `u` with `changeGL * u * changeGL⁻¹`.
- When `0 < f < n`, every element of the conjugate by `changeGL` of the
  upper unipotent radical for `(f, n - f)` is `stdToGL x` for some element
  `x` of the first-block radical `coarseN`. This uses the entrywise formulas
  for the two-block radical.
