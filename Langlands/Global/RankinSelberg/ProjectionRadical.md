# The radicals `Y_(r+1,j)` of the projection and their columns

Module `Langlands.Global.RankinSelberg.ProjectionRadical`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. It is internal matrix algebra and compactness
for the column induction of `ProjectionExpansion`. No literature source is cited for it.

The Library's `projectionUnipotent F (r + 1) j` is `blockUnipotent` for
`projectionWeight (r + 1) j`, the radical `Y_(r+1,j)` of the parabolic of type
`(j + 1, 1, …, 1)`. In `blockUnipotentSubgroup A e` the entries `(a, b)` with `e a ≤ e b` are
those of the identity.

## Matrices

- `projectionWeight_le_iff`: `e_j(a) ≤ e_j(b)` iff `b ≤ j` or `b ≤ a`.
  `projectionWeight_mono`: this order for `j` implies the order for `j + 1`. This is the
  hypothesis `hw` of the block semidirect product, with `Y_(r+1,j+1)` normal in `Y_(r+1,j)`.
- `mem_projectionSubgroup_iff`: `Y_(r+1,j)` consists of the upper unitriangular matrices whose
  first `j + 1` columns are those of the identity.
- `mem_columnSubgroup_iff`: the block Levi part
  `blockUnipotentSubgroup e_j ⊓ blockLeviSubgroup e_(j+1)` consists of the matrices equal to the
  identity outside column `j + 1` above row `j + 1`.
- `colMatrix j c` has the entries of `c` in column `j + 1`, rows `≤ j`, and zeros elsewhere.
  `IsColSupported j c` means `c a = 0` for `a ≥ j + 1`. Proved: additivity, `C C' = 0`,
  unitriangularity of `1 + colMatrix j c`, and `(1 + C c)(1 + C d) = 1 + C (c + d)`.
  `padGL_mul_colMatrix` gives `P · colMatrix c = colMatrix (P c) · P` for `P = diag(g, I)` with
  `g` of size `j + 1` and supported `c`. `isColSupported_padGL_mulVec` says that `P c` is again
  supported.

## Points and compactness

- `mem_projectionAdelic_iff` and `mem_projectionRational_iff` restate the matrix description
  on adelic and rational points, via the Library's `mem_blockUnipotent_affinePoints_iff`.
- `exists_projection_reduction`: let `D ⊆ 𝔸` with `F + D = 𝔸`. For an adelic matrix `N` of the
  shape of `Y_(r+1,j)`, there is a rational matrix `ρ` of the same shape such that every entry of
  `ρ N` above the diagonal in a column after `j` lies in `D`. The proof applies the Library's
  `PrimitiveAdelicHeight.exists_column_step` to the columns `j + 1, …, r` in turn. The step
  changes only the current column, so `ρ` keeps the identity in the first `j + 1` columns.
- `isCompact_projectionBox`: for compact `D`, the set of matrices of this shape with those
  entries in `D` is a product of compact sets.
- `compactSpace_projectionRationalQuotient`: `Y_(r+1,j)(F) \ Y_(r+1,j)(𝔸)` is compact. The
  Library's `exists_isCompact_algebraMap_add_mem` gives a compact `D`. The reduction moves every
  point into the preimage of this compact set, by the method of `compactSpace_unipotentRationalQuotient`
  (module `UnfoldingWhittaker`).
