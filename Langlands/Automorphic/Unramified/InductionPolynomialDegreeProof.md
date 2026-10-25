# Full degree of induced determinant-polynomial products

Author: Worker 398.

This module proves the published closed proposition
`Langlands.Automorphic.Unramified.InductionPolynomialDegreeStatement` without
changing its statement or hypotheses. Its theorem is
`Langlands.Automorphic.Unramified.inductionPolynomialDegree`.

The proof uses only finite polynomial algebra. A nonzero matrix determinant
forces the constant coefficient of its characteristic polynomial to be nonzero,
by `Matrix.det_eq_sign_charpoly_coeff`. Therefore its natural trailing degree
is zero. `Matrix.reverse_charpoly` and `Polynomial.reverse_natDegree` show that
the normalized determinant polynomial has the same natural degree as the
characteristic polynomial, namely the matrix rank. Composition with `X ^ f i`
multiplies this degree by `f i`. Evaluating each composed polynomial at zero
gives one, using positivity of `f i`, so every factor is nonzero. The natural
degree of their finite product is the sum of the individual natural degrees.
The same formulas include empty families and matrices of rank zero.

This is a derived algebraic proof of the degree prerequisite documented in
`TraceAlgebraStatement.md`. Its provenance is the existing Mathlib determinant,
characteristic-polynomial, reversal and degree identities. It does not use the
trace equivalence targets or an automorphic theorem. The original-source
motivation and the normalization `charpolyRev A = det (1 - X • A.map C)` remain
in the imported statement pair; no claim of a new transcription from the
original literature is made here.
