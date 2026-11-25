# Diagonal local isotropy under extension and in low ranks

Local isotropy of a diagonal form over a number field persists under
extension of the number field. The implementation sends each nonzero
isotropic vector through the completion embedding at the place below
the chosen place. The embedding is injective and commutes with the two
maps on the original coefficients.

A zero-dimensional form and a one-dimensional form with nonzero
coefficient have no nonzero zeros over any completion. Over a field,
a binary diagonal form with \(w_0 \ne 0\) has a nonzero zero if and
only if \(-w_1/w_0\) is a square. Over a field of characteristic
zero, a ternary diagonal form with \(w_0,w_1 \ne 0\) has a nonzero
zero if and only if \(x^2-(-w_1/w_0)y^2=-w_2/w_0\) has a solution.
The diagonal local-to-global applications of both tests assume that
every coefficient is nonzero. The binary case reflects squares from
the finite completions, and the ternary case uses the supplied
quadratic norm principle.

The same ternary computation and the cofinite quadratic norm theorem give
isotropy at almost every finite place for diagonal forms over number
fields with at least three variables and all coefficients nonzero. For
each extra coordinate, prepend zero to the isotropic vector.

`NumberFieldDiagonalRankFourIsotropyStatement` expresses diagonal
local-to-global isotropy for four nonzero coefficients over a number field.
`diagonalIsotropy_of_norm_and_rankFour` uses it and the quadratic norm
principle as premises. The proof inducts on dimension. In dimensions at
least five, the tail after the first two coefficients has dimension at
least three and hence satisfies the cofinite condition of the
weak-approximation step. That step applies the induction hypothesis to
the form obtained by replacing the first two coefficients by a single
represented nonzero value.

These are the low-rank and cofinite steps of the proof of Voight,
*Quaternion Algebras*, Theorem 26.8.24, printed p. 451. The ternary step
uses the norm equation in the precise square-root coordinates of
`QuadraticNormEquation`.

Source ID `voight-2021-quaternion-algebras`, SHA-256
`f6c56f6ca7b4bee139b88865a3cf045f899da59d0217618c4dc81daf19ef1ad4`.
