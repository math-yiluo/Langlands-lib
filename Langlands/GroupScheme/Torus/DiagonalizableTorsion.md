# Actual integer torsion of diagonalizable groups

Worker 508.

This internal construction identifies the actual scheme-theoretic kernel
`D_R(M)[n]` with `D_R(M/nM)` over every commutative ring `R`, for every abelian
group `M` and every natural number `n`. It uses the unsaturated quotient by the
subgroup of `n`-multiples, preserving all torsion and infinitesimal structure.
No reducedness, smoothness or characteristic hypothesis is imposed.

The implementation compares points on every test scheme. The published
`torsionPointsEquiv` identifies points of the torsion scheme with sections whose
`n`th power is the identity. The published character point model of a
diagonalizable group identifies this condition with annihilation of all
`n`-multiples in `M`. The full quotient-character equivalence then gives the same
model for `D_R(M/nM)`. Both comparisons are natural under every change of test
scheme, so `isoOfPointModels` constructs `Diagonalizable.torsionIso`.

For finitely generated `M` and `n > 0`, the published
`FiniteCharacterSeparation.finite_quotient` makes `M/nM` finite. Finiteness of the
diagonalizable model and transport through `torsionIso` give `torsion_isFinite`.
The construction is derived from the published torsion, diagonalizable point
model, quotient-character and finite-quotient constructions. It restates no
external theorem.
