# Actual diagonal blocks in the dominant rectangular matrix

This is derived matrix infrastructure for Jacquet–Piatetski-Shapiro–Shalika
(1983), Section 4.10(2), printed page 419. The source supplies the five-block
matrix already implemented in `TwoBlockDominantRectangularData`. This module
aligns its columns by a fixed right permutation and proves an exact
diagonal-block factorization at every element of the supplied two-block Levi.
The auxiliary coordinate maps and factorization are internal derivations,
rather than separately stated theorems in the source. Convergence, compact
support, volume estimates and integrability are separate obligations.

Work over an arbitrary field `K : Type uF`. Put
`a = m 0 + 1` and `b = m 1 + 1`. The hypotheses are
`h : ∑ i, (m i + 1) = t + 1` and `hr : r = t + (j + k + 1)`,
so `a + b = t + 1` and the ambient rank is `r + 1 = a + b + j + k + 1`.
Both actual Levi block ranks are positive; the complementary dimensions `j`
and `k` are arbitrary naturals, including zero.

`diagonalRightPermutation h hr` is
`weylLong (r + 1) K * blockWeyl h hr`. All permutation matrices use the
Library's unsigned convention. `blockWeyl_append_levi` conjugates the actual
appended Levi embedding of `b₀,b₁` through `blockWeyl`. In the published
source coordinates `(a,k,1,j,b)`, the result has the reversed conjugates
`w_a b₀ w_a` and `w_b b₁ w_b` in the outer blocks, identity in the middle,
and zero other entries. Its proof evaluates all block entries using the
published reflection, append and Levi embedding formulas.

`matrix_levi_reversed_entry` evaluates the actual dominant matrix multiplied
on the right by the inverse of `diagonalRightPermutation`. In coordinates
obtained by reversing the full source index, its entries are those of
the three-block matrix

```text
[ w_a b₀ w_a     padX(x)       0                  ]
[ 0             I             padY(y) w_b b₁ w_b ]
[ 0             0             w_b b₁ w_b         ].
```

Here the middle block has coordinates `(k,1,j)`. The proof regroups the
actual matrix product, applies `blockWeyl_append_levi`, and multiplies the
published three-block matrices. `padX_mul_padY` gives the required zero
cross term.

`sourceReversal` reverses the order of all five blocks and every internal
finite index. `leadingCoordinates` and `trailingCoordinates` put the two
resulting groups of coordinates in consecutive standard order.
`diagonalBlocksRank` proves their ranks sum to `r + 1`.
`diagonalBlocksCoordinates_sourceReversal` identifies this explicit
coordinate construction with the actual full `Fin.rev`; its proof checks
the five index cases arithmetically.

`trailingBlockUnit A X` is the invertible block matrix `[I_k,0;X,A]`
on `Fin k ⊕ Fin a`. Its inverse is `[I_k,0;-A⁻¹X,A⁻¹]`, checked by
block multiplication. `trailingBlock` reindexes it to consecutive standard
coordinates. `leadingBlock_entry` computes `unequalRankMatrix j 0 B Y`
as `[B,0,0;Y,I_j,0;0,0,1]`.
`reverse_rectangle_mul` identifies full reversal of `y (w_b B w_b)`
with `y.submatrix Fin.rev Fin.rev * B`.
`diagonalBlocks_entry` evaluates the standard block sum of these two
invertible matrices in their explicit sum coordinates.

Finally, write `xʳ = x.submatrix Fin.rev Fin.rev`,
`yʳ = y.submatrix Fin.rev Fin.rev`, and
`Q = diagonalRightPermutation h hr`.
`matrix_levi_diagonalBlocks` proves the actual group equality

```text
matrix h hr (leviEmbedding b) x y * Q⁻¹
  = reindex (finCongr (diagonalBlocksRank h hr))
      (blockSum (unequalRankMatrix j 0 (b 1) (yʳ * (b 1).val),
                 trailingBlock (b 0) xʳ)).
```

The leading rank is `m 1 + (j + 0 + 1) + 1`, retaining the singleton,
and the trailing rank is `k + m 0 + 1`. The proof combines the reversed
entry formula with the coordinate identity and checks the 25 pairs of
the five source blocks. It applies `reverse_rectangle_mul` in the surviving
rectangle case. No diagonal or torus restriction is imposed on either
supplied Levi element, and no positivity condition is imposed on `j` or `k`.
