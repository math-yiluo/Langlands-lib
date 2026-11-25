# The noncompact picture: right derivatives on the lower unipotent group

## Definitions

- `Lw n`: the positions `(a, b)` with `b < a` (strictly below the diagonal).
- `lowMat w`: the strictly lower triangular matrix with entries `w`; `nbMat v = 1 + lowMat v`,
  the lower unipotent matrix with coordinates `v : Lw n → ℂ`, and the unit `nbUnit v`;
  `lowCoords M`: the strictly lower entries of a matrix; `lowMatCLM`: `lowMat` as a real-linear
  map.
- `diagPart`, `upperPart`: the diagonal and strictly upper parts of a matrix.

## Results

- `nbMat_det` (`= 1`), `isUnit_nbMat`, `nbUnit_mem_lowerUnipotent`, `exists_nbUnit_eq`: the
  `nbUnit v` are exactly the elements of the Library's `lowerUnipotent n ℂ`.
- `isPolyMat_nbMat`: `nbMat` has degree `1` in `v`; `nbMat_inv`: its inverse is its adjugate;
  `isPolyMat_nbMat_inv`: the inverse has degree `≤ n`.
- `eq_upper_add_diag_add_low`: `Y = upperPart Y + diagPart Y + lowMat (lowCoords Y)`.
- `rightDerivative_nbMat`: let `f` lie in `principalSeries ℂ n χ` with
  `principalSeriesCharacter χ 1 = 1`, and suppose the derivative of the extension
  `unitsExtension f` at units `y` in the direction `diag(d) y` is `Λ d · f y`. Then for every
  `X`,
  `(R(X) f)(nbUnit v) = Λ(diag Y) f(nbUnit v) + D(f ∘ nbUnit)(v)[W v]`,
  with `Y = nbMat v · X · (nbMat v)⁻¹` and `W v = lowCoords (lowMat (lowCoords Y) · nbMat v)`.
  Indeed `nbMat v (1 + t X) = (1 + t Y) nbMat v`; the strictly upper part of `Y` contributes
  nothing because `f` is invariant under the upper unipotent group
  (`ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero`), the diagonal part contributes
  `Λ`, and the strictly lower part moves along the lower unipotent group.

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
