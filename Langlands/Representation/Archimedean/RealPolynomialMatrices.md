# Matrix-valued real polynomial maps

`IsPolyMat d M` says that every entry `v ↦ M v a b` of a matrix-valued map
`M : (ι → ℂ) → Matrix κ κ' ℂ` lies in `degLE ι d` (`RealPolynomialFunctions`).

## Results

- `IsPolyMat.mono`, `isPolyMat_const`, `IsPolyMat.add`, `IsPolyMat.sub`.
- `IsPolyMat.mul`: degrees add under matrix products.
- `IsPolyMat.conjTranspose`, `IsPolyMat.submatrix`.
- `IsPolyMat.det`: the determinant of a `κ × κ` matrix of degree `≤ a` has degree `≤ |κ| a`
  (Leibniz expansion).
- `IsPolyMat.adjugate`: the adjugate has entries of degree `≤ |κ| a` (determinants of the
  matrices with one row replaced by a standard basis vector).

## Provenance

Internal infrastructure of Task 7064 for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
