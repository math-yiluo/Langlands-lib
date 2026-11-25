# A degree filtration of block-polynomial principal-series functions

Fix `i ≠ r`, bidegree bounds `p, q`, positive real weights `T_m` (`m : κ`) on the coordinates of
the lower unipotent group, exponents `σ_m` and a slope `c`.

## Definitions

- `conjMat X v = nbMat v · X · (nbMat v)⁻¹` and the vector field `fieldW X v` of
  `ComplexNoncompactPicture.rightDerivative_nbMat`.
- `filtrationLevel χ hir p q T σ c N`: the subspace of functions `F` that lie in
  `principalSeries ℂ n χ`, are block-polynomial of bidegree `< (p, q)` for the root `(r, i)`, and
  satisfy, for some `P ∈ degLE (Lw n) (c (N + 1))` and all `v`,
  `F(nbUnit v) · (∏_m T_m(v))^N = (∏_m T_m(v)^{σ_m}) · P(v)`.

## Results

- `principalSeriesCharacter_one`: for `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}` the normalized
  character is `1` at the identity.
- `isPolyMat_conjMat` (degree `≤ n + 1`), `coord_fieldW_mem` (degree `≤ n + 2`),
  `re_mem_degLE`, `im_mem_degLE`, `torusDeriv_conjMat_mem` (degree `≤ n + 1`).
- `filtrationLevel_mono`: if the `T_m` have degree `≤ e` and `|κ| e ≤ c`, the levels increase
  (multiply `P` by `∏_m T_m`).
- `rightDerivative_mem_filtrationLevel`: if moreover the `T_m` are positive real and
  `(n + 1) + (n + 2) + |κ| e ≤ c`, right derivatives map level `N` to level `N + 1`. By
  `rightDerivative_nbMat` and `fderiv_unitsExtension_diagonal_mul`,
  `R(X)F(nbUnit v) = torusDeriv(diag conjMat) F(nbUnit v) + D(F ∘ nbUnit)(v)[fieldW X v]`; the
  second term is handled by `exists_fderiv_weighted`, the first multiplies `P` by a polynomial
  of degree `≤ n + 1` and by `∏ T_m`. Principal-series membership and block polynomiality are
  preserved by `rightDerivative_mem_principalSeries` and `isBlockPoly_rightDerivative`.

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
