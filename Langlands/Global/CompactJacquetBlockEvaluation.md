# Jacquet equations for normalized block evaluations

For an evaluation into a Levi coefficient module,
`IsNormalizedBlockLieEvaluation` gives its covariance on upper triangular
matrix directions. It sums the coefficient actions of the diagonal block
restrictions and adds the scalar from the differential of the outer
half-modulus. `blockHalfDifferential_real` and
`blockHalfDifferential_complex` identify that scalar with the values in
`AdelicBlockParabolicPlaceDifferential` for the real and complex places.

When the ambient direction is strictly upper triangular, each block
restriction is strictly upper triangular and every block trace is zero.
For a single diagonal direction in block \(i\), the other block
restrictions vanish. The scalar then shifts the real diagonal exponent
by the outer half exponent at a real place and by twice that exponent
at a complex place. An imaginary diagonal direction contributes zero
to the real part of the block trace.

The real sign and position exponent come from the same block and
position in the ordered concatenation. The two Jacquet functional
theorems combine these computations with the block probe equations.
The real theorem takes the compact sign equation on the evaluation as
an input. The complex theorem uses a specified list of characters in
position order and their two diagonal eigenvalues.

These are derived algebraic implications for the compact Jacquet
comparison. The differential normalization uses
`BlockPrincipalSeriesNormalization` and
`AdelicBlockParabolicPlaceDifferential`. The functional equations use
the conventions in `RealJacquetReduction` and `ComplexJacquetReduction`.
