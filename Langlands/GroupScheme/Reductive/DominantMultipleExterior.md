# Exterior powers of diagonal cocharacters

Worker 1161. This is an internal companion to the published
`Chevalley.MatrixExterior`. It computes exterior powers of diagonal matrices and
cocharacters and isolates the unique exterior coordinate of top weight. It is used
to produce normalized covariant coordinates from top weight lines in
`DominantMultipleCoefficients`.

## Exterior powers of diagonal matrices

- `Chevalley.exteriorGL_diagonal`: if an invertible matrix `g` over a commutative
  ring is `diag(w)`, then `exteriorGL N d A g` is the diagonal matrix with entry
  `Π_{a ∈ s} w a` at each `d`-subset `s`. By `exteriorGL_apply`, the `(s, t)` entry
  is the determinant of the `d × d` matrix whose `(i, j)` entry is `g (sⱼ, tᵢ)`.
  Here `sⱼ` and `tᵢ` enumerate `s` and `t` in increasing order, so this is the
  transpose of the minor of `g` with rows in `s` and columns in `t`. For `s = t`
  the matrix is diagonal, with the entries of `w` on `s`. For `s ≠ t`, some element
  `sₖ` of `s` is not in `t`, and column `k` of the matrix vanishes. This follows the pattern of
  Mathlib's `ιMultiDual_apply_nondiag`.
- `Chevalley.units_zpow_sum`: `x ^ (Σ eₐ) = Π x ^ eₐ` for a unit `x`.
- `Chevalley.diagonalCocharacter_comp_exteriorGroupHom`: the composite of the
  diagonal cocharacter of weights `e` with the actual exterior-power group
  homomorphism is the diagonal cocharacter of the weights `s ↦ Σ_{a∈s} e a` on
  `d`-subsets. The equality of group-scheme morphisms is checked on points over
  every test scheme. It uses `exteriorRepresentation_pointMatrix` and the point
  formula `pointsEquiv_diagonalCocharacter`.

## The top subset

For weights `e : Fin N → ℤ` and an integer `M`:

- `topSet e M` is the set of coordinates of weight exactly `M`, `topCard e M` is
  its size, and `topPoint e M` is this set as a point of
  `Set.powersetCard (Fin N) (topCard e M)`.
- `sum_topPoint`: the weight sum over the top subset is `topCard e M * M`.
- `sum_lt_sum_topPoint`: if `M` bounds all weights, every other subset of the same
  size has strictly smaller weight sum. Such a subset contains some coordinate of
  weight `< M`, while all its weights are at most `M`.
