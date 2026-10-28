# Matrix identities for the rank-one extension cells

Module `Langlands.Representation.RankinSelberg.RankOneExtensionCellAlgebra`.

This helper module proves block-matrix identities in `GL_(1+(t+1))(K)`, for an arbitrary
field `K`. They relate the two cell coordinates of the published module
`RankOneExtensionAnalyticData`:

- the upper cell `u(y) = [I_(t+1), y; 0, 1]` (`rankOneExtensionUpperCell t y`), and
- the lower block `B(m, x, a) = [m, 0; x, a]` (`rankOneExtensionLowerBlock t m x a`),
  with `m ∈ GL_(t+1)`, a row `x`, and a unit `a`.

## Provenance

The identities are elementary matrix computations used in the proof of
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105
(1983), Lemma 5.5 (printed pp. 424–426). There the integral over `N_(t+2) \ GL_(t+2)` is
unfolded in the coordinates `u(y) B(m, x, a)` of the open cell. The exact statements below
are derived for this formalization and are not quoted from the paper.

## Contents

- `rankOneExtensionLowerBlock_entry` gives the numeric entries of `[m, 0; x, a]`.
  This unchanged declaration and proof were moved from `RankOneExtensionSpanTransfer`
  into this algebraic layer so both span transfer and lower covariance reuse it.
- `rankOneExtensionCellBlocks t g` gives the `(Fin (t+1) ⊕ Fin 1)`-indexed block matrix
  of `g`. It is obtained by reindexing along the published equivalence
  `rankOneExtensionCellCoordinates t`. The module proves that it is multiplicative and
  injective, computes its entries, and shows that it recovers `g` and has the same
  determinant as `g` (`rankOneExtensionCellBlocks_val`,
  `det_eq_det_rankOneExtensionCellBlocks`). It also computes the blocks of `u(y)` and of
  `B(m, x, a)`.
- Group law of the cells: `u(y) u(z) = u(y + z)`, `u(0) = 1`, and
  `B(m, x, a) B(m', x', a') = B(m m', x m' + a x', a a')`.
- Conjugation: `B(n, 0, 1) u(z) = u(n z) B(n, 0, 1)`.
- Open-cell exchange (`rankOneExtensionUpperCell_mulVec_mul_lowerBlock`): if
  `m' = m (I + y₁ x)` and `a' (1 + x · y₁) = a`, then
  `u(m y₁) B(m, x, a) = B(m', x, a') u(a' y₁)`. This is the identity behind the change of
  variables `(m, a, y₁) ↦ (m', a', a' y₁)` that moves the upper cell from the left of the
  lower block to its right.
- Determinants: `det B(m, x, a) = det m · a` and `det u(y) = 1`.
- Upper unipotence in block coordinates (`mem_upperUnipotent_iff_cellBlocks`). As
  consequences, `u(y)` and `B(n, 0, 1)` for upper unipotent `n` are upper unipotent.
- Decomposition of the upper unipotent group: every `n ∈ N_(1+(t+1))` equals
  `u(y₀) B(n'', 0, 1)`. Here `n''` (`rankOneExtensionUnipotentHead n`) is the upper-left
  block, which is upper unipotent in `GL_(t+1)`, and `y₀`
  (`rankOneExtensionUnipotentColumn n`) is the last column above the diagonal.

## Proof method

Every group identity is proved by applying the injective map `rankOneExtensionCellBlocks`
and comparing the four blocks of `Matrix.fromBlocks` products entrywise. The open-cell
exchange uses the vector identity
`m (I + y₁ x) (a' y₁) = a' (1 + x · y₁) m y₁ = a m y₁`. The upper-unipotence
characterization transports the published entrywise definition of `upperUnipotent`
along `rankOneExtensionCellCoordinates`. For that it uses the explicit values of the
coordinate indices: `i` for the large block and `t + 1` for the scalar block. The
determinant of the unipotent head is `1` because the head is upper triangular with unit
diagonal.
