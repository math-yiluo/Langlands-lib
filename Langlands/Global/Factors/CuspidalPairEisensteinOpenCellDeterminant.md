# The second Levi block on the open cell

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellDeterminant`, namespace
`Langlands.Global.CuspidalPairEisenstein.OpenCellDeterminant`.

Let `N = r + t + 2`, let `w = openCellWeyl F r t` and `u'(Y) = openCellUnipotent F r t Y` be the
matrices of [CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md), and let
`w u'(Y) = p k` with `p` in the upper parabolic `P` of block sizes `(r + 1, t + 1)` and `k` in the
standard maximal compact subgroup `standardCompact F N`. Let `m₂` be the second diagonal block of
`p` (`Oneplace.leviSnd` of the Levi projection). For every `e ≥ 0` the module bounds
`|det m₂|_𝔸^(-e)` by a constant times the majorant `Ω_e(Y)` of
[CuspidalPairEisensteinOpenCellMajorant.md](CuspidalPairEisensteinOpenCellMajorant.md). The
condition `e ≥ 0` is needed: the bound comes from a lower bound for `|det m₂|_𝔸`, which is
reversed by raising to the nonpositive power `-e`.

## Content

Rows of the open cell:

- `rowIndex r a` (the row `r + 1 + a` of the second block, `rowIndex_val`), `leftColumn r j`
  (column `j < t + 1`), `rightColumn t j` (column `t + 1 + j`, `j < r + 1`).
- `openCellWeyl_rowIndex_apply`, `openCellWeyl_mul_rowIndex_apply` (row `r + 1 + a` of `w M` is
  row `a` of `M`), `openCell_rowIndex_leftColumn` and `openCell_rowIndex_rightColumn`: the last
  `t + 1` rows of `w u'(Y)` are `[I_(t+1) | Y]`.
- `blockInverse p`, the matrix of `A = m₂⁻¹`; `rowIndex_apply_of_mul_eq`: if `p k = g`, then
  row `r + 1 + a` of `k` is `∑_e A_(a e)` times row `r + 1 + e` of `g` (the lower left block of
  `p⁻¹` vanishes, `BlockShape.mem_parabolic_iff`, and its lower right block is `A`).
- `compact_rowIndex_leftColumn`, `compact_rowIndex_rightColumn`: for `p k = w u'(Y)` the last
  `t + 1` rows of `k` are `[A | A Y]`.

Finite places (`v`, with `‖·‖_v` the norm of `F_v`):

- `finiteProjection_mem_of_mem_standardCompact`: entries of `k ∈ standardCompact` are integral
  at every finite place.
- `norm_det_le_one_and_adjugate`: a matrix over `F_v` with integral entries has integral
  determinant and adjugate.
- **`max_one_entryNorm_le_norm_det`**: `max(1, ‖Y_v‖) ≤ |det m₂|_v`.

Archimedean places:

- `norm_infiniteProjection_le_one`: entries of `k ∈ standardCompact` have norm at most `1` at
  every archimedean place.
- `norm_det_le_factorial_and_adjugate`: over a normed field, a `m × m` matrix with entries of norm
  at most `1` has determinant and adjugate entries of norm at most `m!`.
- `archEntryNorm v Y`, the maximum norm of the entries of `Y` at the archimedean place `v`;
  `norm_le_archEntryNorm`, `archEntryNorm_le_iff`.
- **`max_one_archEntryNorm_le_norm_det`**: `max(1, ‖Y_v‖) ≤ (t + 2)! · |det m₂|_v`.

Global bound:

- `absDet_eq_prod`: `|det g|_𝔸 = ∏_(v | ∞) |det g_v|_v^(m_v) · ∏ᶠ_(v finite) |det g_v|_v`, with
  `m_v = InfinitePlace.mult v`.
- `mulSupport_norm_det_finite`, `mulSupport_max_one_entryNorm_finite`,
  `finprod_le_finprod_of_one_le`, `finprod_rpow_of_one_le`, `one_le_finprod_of_one_le`: finite
  products over the finite places.
- `prod_rpow_neg_le_archWeight`: for `e ≥ 0`,
  `(∏_(v | ∞) max(1, ‖Y_v‖)^(m_v))^(-e) ≤ 2^e (1 + ‖Y_∞‖)^(-e)`.
- **`rpow_neg_absDet_le_majorant`**: if `w u'(Y) = p k` with `k ∈ standardCompact F N` and
  `e ≥ 0`, then `|det m₂|_𝔸^(-e) ≤ (((t + 2)!)^d)^e · 2^e · Ω_e(Y)` with `d = [F : ℚ]`.

## Proofs

- `openCellWeyl_rowIndex_apply`: `w` is the permutation matrix of
  `Shahidi.blockWeylPermutation`, and the inverse permutation sends `r + 1 + a` to `a`
  (`Shahidi.blockWeylPermutation_symm_second`). The rows of `u'(Y)` are read off from
  `openCellUnipotent_apply` and `Shahidi.upper_first_first`, `Shahidi.upper_first_second`.
- `rowIndex_apply_of_mul_eq`: `k = p⁻¹ g`; the sum over the columns of `p⁻¹` is split by blocks
  (`BlockShape.indexEquiv`), the first block contributes `0` and the second block gives the
  entries of the second Levi block of `p⁻¹`, which is `m₂⁻¹`.
- `max_one_entryNorm_le_norm_det`: let `A_v` be the component of `A` at `v`. Its entries and those
  of `A_v Y_v` are entries of `k_v`, hence integral. So `|det A_v| ≤ 1`, and from
  `det(A_v) Y_v = adj(A_v) (A_v Y_v)` and the ultrametric inequality,
  `|det A_v| · |(Y_v)_(a j)| ≤ 1`. Since `det m₂,v · det A_v = 1`, both `1` and every entry norm
  of `Y_v` are at most `|det A_v|⁻¹ = |det m₂|_v`.
- `norm_infiniteProjection_le_one`: the archimedean component of `k` is the image of real
  orthogonal and complex unitary matrices (`standardInfiniteCompact`); in the mixed coordinates
  the entries are entries of unitary matrices (`entry_norm_bound_of_unitary`), and the extension
  embeddings of the completions are isometries.
- `norm_det_le_factorial_and_adjugate`: `Matrix.det_le` for the absolute value of the norm; an
  adjugate entry is the determinant of a matrix with one row replaced by a standard basis row
  (`Matrix.adjugate_apply`).
- `max_one_archEntryNorm_le_norm_det`: as at the finite places, with `|det A_v| ≤ (t + 1)!` and
  `|det A_v| · |(Y_v)_(a j)| ≤ (t + 1) · (t + 1)! ≤ (t + 2)!` from the triangle inequality.
- `absDet_eq_prod`: `IdeleAbsoluteValue.coe_full` and compatibility of the determinant with the
  projections to the completions (`RingHom.map_det`).
- `prod_rpow_neg_le_archWeight`: at a place `v₀` where `max(1, ‖Y_v‖)` is largest,
  `1 + ‖Y_∞‖ ≤ 2 max(1, ‖Y_(v₀)‖)` (the mixed-space norm is the maximum of the coordinate norms,
  and the extension embeddings are isometries), and
  `max(1, ‖Y_(v₀)‖) ≤ ∏_v max(1, ‖Y_v‖)^(m_v)` since all factors are at least `1`.
- `rpow_neg_absDet_le_majorant`: multiplying the local bounds,
  `∏_(v | ∞) max(1, ‖Y_v‖)^(m_v) · ∏_v max(1, ‖Y_v‖) ≤ ((t + 2)!)^d · |det m₂|_𝔸`
  (`∑_v m_v = d`, `InfinitePlace.sum_mult_eq`; the finite products are compared over a finite
  set containing both supports). Since `e ≥ 0`, raising both sides to the nonpositive power
  `-e` reverses this inequality (`Real.rpow_le_rpow_of_nonpos`), so `|det m₂|_𝔸^(-e)` is at
  most `((t + 2)!^d)^e` times the `(-e)`-th power of the left side. Splitting the finite
  product (`finprod_rpow_of_one_le`) gives the archimedean factor, bounded by
  `prod_rpow_neg_le_archWeight` (which also uses `e ≥ 0`), times `finiteWeight e Y`.

## Provenance

The bound expresses that `δ_P(m)` on the open cell `P w U'` decays like a power of the height of
`Y`. Decay of this kind is what makes intertwining integrals converge for `Re(s)` large, and
such integrals dominate the local components of the Fourier coefficient in Shahidi, *On certain
L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`), proof of Theorem 5.1,
p. 352. Here the decay is stated against the product majorant `Ω_e`; the comparison with `Ω_e`
and the proof through the last rows `[A | A Y]` of the compact factor are internal to the formal
proof.
