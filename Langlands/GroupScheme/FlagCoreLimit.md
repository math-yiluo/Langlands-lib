# Lowest-weight limits of homogeneous polynomial equations

Helper module for the covering core of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. It holds the
elementary polynomial algebra behind the limit argument in the proof of Milne,
*Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, Theorem 17.65
(printed pp. 374-375). There a cocharacter `λ` of a maximal torus moves a point of
a closed orbit in projective space to its limit `lim_{z → 0} λ(z) · x`, and the
limit stays in the orbit closure. This module proves the coordinate version of
that step for any homogeneous equation.

## Definitions

- `weightPart d v c`: for integer weights `d : σ → ℤ`, a vector `v : σ → k` and an
  integer `c`, the vector that agrees with `v` on the coordinates `i` with
  `d i = c` and is zero on the others. When `c` is the least weight occurring in
  `v`, this is the coordinate form of the limit `lim_{z → 0} λ(z) · [v]` for a
  cocharacter `λ` acting by `z ↦ diag(z ^ d i)`.

## Results

- `eval_smul_of_isHomogeneous`: if `f` is homogeneous of degree `m`, then
  `f(a • x) = a ^ m * f(x)`.
- `eval_weightPart_eq_zero` (limit lemma): let `k` be an infinite field and `f` a
  homogeneous polynomial. Suppose `c ≤ d i` whenever `v i ≠ 0`, and
  `f((z ^ d i * v i)_i) = 0` for every `z ≠ 0`. Then `f(weightPart d v c) = 0`.

## Proof of the limit lemma

Write `e i = (d i - c).toNat`. Substituting `X_i ↦ v i * T ^ e i` in `f` gives a
one-variable polynomial `P`. When `v i ≠ 0` we have `d i = c + e i`, so
`(z ^ d i * v i)_i = z ^ c • (v i * z ^ e i)_i`. By homogeneity, `P(z)` is a
nonzero multiple of `f((z ^ d i * v i)_i)`, so `P` vanishes at every `z ≠ 0`. An
infinite field has infinitely many such `z`, so `P = 0`. Finally
`weightPart d v c = (v i * 0 ^ e i)_i`, because `0 ^ e i` is `1` exactly when
`e i = 0`, that is `d i = c` (for `v i ≠ 0`). Hence
`f(weightPart d v c) = P(0) = 0`.

## Provenance

These are internal helper definitions and lemmas with no counterpart in the
literature. Milne's proof takes the limit of `λ(z) · x` geometrically. Here the
same step is done on coordinates, so that it can be applied to the homogeneous
equations of a closed orbit, which are described in
`Langlands.AlgebraicGeometry.ProjectiveSpace.RationalPointZeros`.

`weightPart` reuses `GeneralLinear.weightPart` from
`Dynamic/GeneralLinearWeightComponents`, with its last two arguments
reordered. The common coordinate operation is unchanged.
