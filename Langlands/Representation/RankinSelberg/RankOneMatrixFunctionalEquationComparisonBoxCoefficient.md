# Pointwise compact averaging on a rank-one matrix box

Worker 396. Internal derived helper for the matrix functional-equation comparison.

The determinant-rank-one endomorphism sends `g` to
`diag(det(g),1,…,1)` and is continuous. If a principal level fixes the
model vector both directly and through this endomorphism, then on the
published rank-one box the actual model function equals its value at that
diagonal. The box hypotheses ensure that the standard character is trivial
on its unipotent factor. Row replacement removes a right principal-level
element, and the published upper-triangular parametrization then removes
the torus and unipotent factors. Applying the determinant endomorphism to
the removed right element preserves the value by the second stabilizer
hypothesis.

The normalized compact average equals the original function at every point
where all left translates in the subgroup have that value. This is a
pointwise equality from integration of a constant and the exact finite,
positive Haar mass. It makes no inference from integrability of an average
to integrability of the original function.

These are derived consequences of the published box decomposition and
actual model equivariance. No original-source transcription is asserted.
Convergence and the final matrix-to-block functional equation are not yet
conclusions of this module.

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxCoefficient` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
