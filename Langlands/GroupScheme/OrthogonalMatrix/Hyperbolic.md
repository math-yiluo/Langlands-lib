# Hyperbolic bases over algebraically closed fields

This internal module supports the proof of
`Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryStatement`. It shows
that over an algebraically closed field `L` every quadratic form on an even-dimensional
finite-dimensional vector space whose polar form is nondegenerate is split (hyperbolic).
The even dimension is needed: over `ℂ` the form `x ↦ x ^ 2` on a line has nondegenerate
polar form but no nonzero isotropic vector. The argument works in every characteristic,
including characteristic `2`. The argument is the standard splitting off of
hyperbolic planes. It is derived here because Mathlib has no hyperbolic or Witt
decomposition for quadratic forms that also covers characteristic `2`. Statements
use Mathlib's `QuadraticForm`, `QuadraticMap.polar` and `QuadraticMap.polarBilin`, and
the matrices `formMatrix` and `polarMatrix` of
`Langlands.GroupScheme.OrthogonalMatrix.Basic`.

## Isotropic vectors and hyperbolic pairs

- `quadratic_add_smul`: `Q (x + t • y) = Q x + t * polar Q x y + t * t * Q y`.
- `exists_isotropic`: if `L` is algebraically closed and `1 < finrank L V`, every
  quadratic form `Q` on `V` has a nonzero vector `e` with `Q e = 0`. The proof takes
  two linearly independent vectors `x, y`. If `Q y = 0`, then `e = y`. Otherwise the
  polynomial `Q y · X² + polar Q x y · X + Q x` has degree two and so has a root `t`,
  and `e = x + t • y`. No division by `2` is needed.
- `exists_hyperbolicPair`: if moreover the polar bilinear form is left separating,
  there are `e, f` with `Q e = Q f = 0` and `polar Q e f = 1`. The proof takes an
  isotropic `e ≠ 0` and a `z` with `polar Q e z ≠ 0`. Let `f'` be `z` rescaled so that
  `polar Q e f' = 1`. Then `f = f' - Q f' • e`.

## Hyperbolic families

`exists_hyperbolicFamily_aux` (by induction on `k`) and its restatement
`exists_hyperbolicFamily` say: if `finrank L V = 2 * k` and
`QuadraticMap.polarBilin Q` is nondegenerate, there is a family
`v : Fin k ⊕ Fin k → V` with `Q (v a) = 0` for all `a`, and
`polar Q (v a) (v b) = polarMatrix (Fin k) L a b` (the Gram matrix `[[0, 1], [1, 0]]`).

In the induction step, `x, f` is a hyperbolic pair spanning a plane `W`. The
restriction of the polar form to `W` is nondegenerate. Since the polar form is
reflexive, Mathlib's `isCompl_orthogonal_of_restrict_nondegenerate` makes `W` and its
orthogonal `W'` complementary. The form on `W'` is again nondegenerate
(`restrict_nondegenerate_iff_isCompl_orthogonal` with `orthogonal_orthogonal`), and
`W'` has dimension `2 k`. The induction hypothesis applied to `Q` restricted to `W'`
gives a family on `W'`. Prepending `x` to the `inl` part and `f` to the `inr` part
gives the family on `V`.

## Matrix form

`of_mul_mul_transpose_apply` computes the entries of `P C Pᵀ` for the matrix `P` with
rows `v a`: they are `v a ⬝ᵥ C *ᵥ v b`.

`exists_hyperbolic_matrix`: let `L` be algebraically closed, `n` a finite type with
`Fintype.card n = 2 * m`, and `Q : Matrix n n L` with `Q + Qᵀ` invertible. Then there
are `P : Matrix (Fin m ⊕ Fin m) n L` and `P' : Matrix n (Fin m ⊕ Fin m) L` with
`P * P' = 1`, `P' * P = 1` and `P * Q * Pᵀ - formMatrix (Fin m) L` alternating
(`IsAlt`). In other words, the change of coordinates `P` carries the quadratic form
`x ↦ x Q xᵀ` to the split form `∑ a, x (inl a) * x (inr a)`.

The proof applies `exists_hyperbolicFamily` to the quadratic form
`x ↦ x ⬝ᵥ Q *ᵥ x` on `n → L`. Its polar form is the bilinear form of `Q + Qᵀ`, which is
nondegenerate because `det (Q + Qᵀ) ≠ 0`. Take `P` to be the matrix whose rows are the
family. Then `P (Q + Qᵀ) Pᵀ = polarMatrix`, and since `polarMatrix² = 1` the matrix
`P' = (Q + Qᵀ) Pᵀ polarMatrix` is a right inverse of `P`. The square case of
`Matrix.mul_eq_one_comm_of_equiv` makes it a left inverse too. Finally, `isAlt_iff`
shows that `P Q Pᵀ - formMatrix` is alternating. Its symmetric part is
`P (Q + Qᵀ) Pᵀ - polarMatrix = 0`. Its diagonal entries are `Q (v a) = 0` minus the
diagonal of `formMatrix`, which is zero.
