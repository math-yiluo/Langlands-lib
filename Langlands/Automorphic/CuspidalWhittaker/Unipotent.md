# Column and block unipotent matrices

Author: Worker 1709.

This is internal matrix algebra for the proof of
`Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement`. It works over an arbitrary
commutative ring `R`, with matrices indexed by `Fin n` (0-indexed). All results are proved,
and no hypothesis is assumed. `Columns`, `WhittakerCoefficient` and `LocalFunctional` use it
with `R = 𝔸_K`.

## Square-zero units

`sqZeroUnit N h` is the unit `1 + N` with inverse `1 − N`, for `N * N = 0`.
`sqZeroUnit_mul_eq` multiplies two such units whose product of nilpotent parts vanishes.

## Column matrices

- `colMat c v` has entry `v i` at `(i, c)` for `i < c` and is zero elsewhere.
- `colUnit c v = 1 + colMat c v` is the column unipotent element.

The module proves the following:

- `colUnit c v * colUnit c w = colUnit c (v + w)`.
- Column elements in the same column commute.
- `colUnit c v` depends only on `v i` for `i < c`.
- Entry formulas for products with arbitrary matrices.
- `mul_colMat_of`: a matrix supported in rows and columns `< c` acts on `colMat c v` through
  `M *ᵥ v`.

## Block matrices

- `blkMat m c X` has entry `X (i, j)` at `(i, j)` for `i < m ≤ j ≤ c`.
- `blkUnit m c X = 1 + blkMat m c X`, and these units multiply by adding coordinates.
- `updateCol X c v` replaces column `c` of the coordinates `X` by `v`.
- `truncVec m v` keeps the coordinates `< m`.

The splitting identities for the block integrals hold for `m ≤ c` and the column
`col = c + 1`:

- `colUnit_truncVec_mul_blkUnit`: `u_col(trunc_m z) · b_{m,c}(X) = b_{m,c+1}(X with column col
  replaced by z)`.
- `colUnit_mul_blkUnit_split`:
  `u_col(y) · b(X) = u_col(trunc_m y − N(y − trunc_m y)) · b(X) · u_col(y − trunc_m y)`,
  where `N = blkMat m c X`.
- `blkUnit_updateCol_mul_colUnit`: moving `u_col(w)` across `b_{m,c+1}(updateCol X col z)`
  changes column `col` of the coordinates to `z + N w`.

## Mirabolic and block conditions

- `IsMir c M`: `M` agrees with the identity in the rows `≥ c` and in the columns `> c`.
- `IsBlk c M`: `M` agrees with the identity in the rows `≥ c` and in the columns `≥ c`.

`IsMir c` is closed under products (`IsMir.mul`). Both conditions are closed under inverses of
invertible matrices (`IsMir.inv`, `IsBlk.inv`). Column and block units satisfy them in the appropriate ranges.
`colUnit_mul_of_isBlk` conjugates a column element by a block matrix:
`u_c(v) g = g u_c(g⁻¹ v)` when `IsBlk c g`.

## Upper unitriangular matrices with trivial first columns

`IsUpperColId c M` means `M i j = δ_{ij}` whenever `j ≤ i` or `j ≤ c`. So `M` is upper
unitriangular and its columns `≤ c` are those of the identity. Two results are used by the
equivariance step:

- `isUpperColId_peel`: multiplying by `u_{c+1}(−y₀)`, where `y₀` is column `c + 1`, clears
  column `c + 1` and keeps the rows `≥ c + 1`.
- `isUpperColId_conj`: conjugation by a column element in column `c + 1` preserves
  `IsUpperColId (c + 1)` and the rows `≥ c + 1`.

## Change of ring and continuity

The constructions commute with `RingHom.mapMatrix` (`map_colUnit`, `map_blkUnit`), and the
conditions are preserved by ring homomorphisms. Over a topological ring, `colMat`, `blkMat`,
`colUnit`, `blkUnit` (as maps into `GL` with its units topology), `updateCol` and `truncVec`
are continuous.
