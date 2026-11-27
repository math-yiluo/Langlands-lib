# The open-cell coordinate of a matrix over a valued field

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellCutoff`, namespace
`Langlands.Global.CuspidalPairEisenstein.OpenCellCutoff`.

The module is local linear algebra for the open Bruhat cell `P w U'` of the upper two-block
parabolic `P` of `GL_(r+t+2)` with blocks `(r + 1, t + 1)`, where `w` is Shahidi's block Weyl
representative `Shahidi.blockWeyl (r+1) (t+1)` and `U'` the exchanged upper radical
`u'(y) = Shahidi.intertwiningUnipotent (r+1) (t+1) y`. It is used to cut a section off, at
finitely many finite places, to the matrices `p w u'(y)` with open-cell coordinate `y` in a
small ball around `0`: a neighbourhood of the coset `P w` in the open chart `P w U'` of
`P \ G`, corresponding to `u'(0) = 1` in `U'`
([CuspidalPairEisensteinSemilocalCutoff.md](CuspidalPairEisensteinSemilocalCutoff.md)).

## Content

For a field `K` and a matrix `g` of size `r + t + 2`:

- Indices: `botIdx r t i = r + 1 + i` (rows of the lower block), `topIdx r t j = j`,
  `leftIdx r t j = j` (columns of the left block of size `t + 1`) and
  `rightIdx r t j = t + 1 + j`; `sum_rows` and `sum_cols` split sums over `Fin (r + t + 2)`
  accordingly.
- Blocks: `botLeft r t g` is the lower left `(t + 1) × (t + 1)` block `A(g)` (rows
  `r + 1, …, r + t + 1`, columns `0, …, t`), `botRight r t g` the lower right
  `(t + 1) × (r + 1)` block `B(g)`, `botBot r t g` the lower right diagonal block of size
  `t + 1`, and `kLL`, `kRL`, `kLR`, `kRR` the four blocks of a matrix for the column blocks
  `(t + 1, r + 1)`.
- `cellCoord r t g = A(g)⁻¹ B(g)` (Mathlib's `Matrix.inv`, which is `0` for singular `A(g)`),
  defined for every matrix `g`. For `g ∈ GL_(r+t+2)(K)` with `A(g)` invertible it is the
  coordinate `y` of the decomposition `g = p w u'(y)` with `p ∈ P(K)`: the lower rows of `g`
  are `A(g) [1, y]`, the lower rows of `w u'(y)` are `[1, y]`, so `g (w u'(y))⁻¹` has
  vanishing lower left block.
- `botLeft_mul_of_lowerZero`, `botRight_mul_of_lowerZero`, `botBot_mul_of_lowerZero`: if the
  lower left `(t + 1) × (r + 1)` block of `p` vanishes, then `A(pg) = D A(g)` and
  `B(pg) = D B(g)` for the lower right block `D` of `p`; `isUnit_det_botBot`: `D` is invertible
  when `p` is; `cellCoord_mul_of_lowerZero`: `A(pg)⁻¹ B(pg) = A(g)⁻¹ B(g)`.
- `botLeft_mul`, `botRight_mul`: the block formulas `A(gk) = A(g) k_LL + B(g) k_RL` and
  `B(gk) = A(g) k_LR + B(g) k_RR`.

For a valuation `v : Valuation K Γ₀`:

- `InCell v r t γ g`: `det A(g) ≠ 0` and every entry of `A(g)⁻¹ B(g)` has valuation `< γ`.
- `inCell_mul_left_iff`: `InCell` is invariant under left multiplication by an invertible
  matrix with vanishing lower left block (for instance an element of the parabolic `P`).
- `ltIdeal γ`, the ideal `{x ∈ 𝒪_v | v x < γ}` of the valuation integers, and
  `det_and_inv_of_close_one`: a square matrix congruent to `1` modulo `γ ≤ 1` has
  determinant of valuation `1` and an inverse with integral entries (reduce the matrix modulo
  `ltIdeal γ` and use the adjugate formula).
- `map_mul_lt_of_lt`, `map_mul_lt_of_lt'`: products of a matrix with entries of valuation
  `< γ` and an integral matrix have entries of valuation `< γ`.
- **`InCell.mul_right`**: for `0 ≠ γ ≤ 1`, if `InCell v r t γ g` and every entry of `k - 1`
  has valuation `< γ`, then `InCell v r t γ (g k)`.
- `openCellMatrix y = w u'(y)` (reindexed to size `r + t + 2`); `botLeft_openCellMatrix`,
  `botRight_openCellMatrix`: `A(w u'(y)) = 1` and `B(w u'(y)) = y`;
  **`inCell_openCellMatrix_iff`**: `InCell v r t γ (w u'(y))` holds exactly when every entry
  of `y` has valuation `< γ`.

## Proof of `InCell.mul_right`

Write `c = A(g)⁻¹ B(g)`, so `B(g) = A(g) c`. By `botLeft_mul` and `botRight_mul`,
`A(gk) = A(g) M` and `B(gk) = A(g) N` with `M = k_LL + c k_RL` and `N = k_LR + c k_RR`.
The entries of `k` are integral (they are within `γ ≤ 1` of the entries of `1`), so `M` is
congruent to `1` and `N` to `0` modulo `γ`. By `det_and_inv_of_close_one`, `det M` has
valuation `1` and `M⁻¹` is integral. Hence `det A(gk) = det A(g) det M ≠ 0` and
`A(gk)⁻¹ B(gk) = M⁻¹ N` has entries of valuation `< γ`.

## Provenance

The decomposition of the open cell `P w U'` and the coordinate `y` of `w u'(y)` follow the
notation of F. Shahidi, *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)*, Amer. J. Math. 106 (1984) (`shahidi-1984-fourier`), printed page 72,
equation (0.2) (the block Weyl element `w` and the radical `U'`), as formalized in
`Langlands.Representation.Shahidi.Geometry`. The cutoff condition `InCell` and the lemmas
about it are elementary linear algebra over a valued field and are internal to the Library.
They serve the finite places of the finite set `S` in the proof of Shahidi (1981),
Theorem 5.1, pp. 351–352 (`shahidi-1981-certain-l`), where Shahidi chooses the local data
with nonzero local value by Proposition 3.1 (p. 332); the Library instead multiplies the
section by the indicator of the matrices `p w u'(y)` with `y` in a small ball around `0` (a
neighbourhood of the coset `P w` in the open chart `P w U'`), which makes the local
contribution an explicit nonzero constant.
