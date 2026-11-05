# Actual real Frechet differential of archimedean algebraic coefficients

This internal construction differentiates the actual point action on the
full coefficient space. It uses the same oriented embedding maps and the
actual generic scheme-representation Frechet differential. No analytic versus
algebraic differential comparison is needed to construct these objects.

`embeddingMatrixLinear` is the actual entrywise oriented embedding algebra
map as a continuous real linear map; continuity follows from the number-field
finite-dimensional source. `orbitCoordinateExtension v` evaluates the actual
matrix representation in its open units chart after this embedding and
multiplies the resulting matrix by v. On every invertible matrix it equals
the original completion-based point action on v.

`orbitDerivative v` composes the actual generic derivative, oriented linear
map and continuous linear multiplication by v. The chain rule proves
`hasFDerivAt_orbitCoordinateExtension` at the identity, with no supplied
derivative or regularity premise. The word analytic here refers to real
Frechet calculus, not a power-series analyticity assertion.

`analyticRealDifferential` is a real linear family of complex-linear
endomorphisms of the entire coefficient space. Its value on X and v is the
actual generic Frechet derivative at the embedded real Lie direction,
followed by matrix multiplication on v. `orbitDerivative_realLie` identifies
that value with the derivative of the actual orbit extension evaluated on
the original real Lie matrix direction. This construction does not bundle a
Lie homomorphism or assume an unproved Lie law.

The conditional theorem `analyticRealDifferential_eq_lie_of_comparison`
records the precise downstream use of the unproved generic
`AnalyticProductDifferentialComparison rho`: if that exact comparison is
proved, the constructed analytic endomorphism equals the existing algebraic
coefficient action of `1 tensor X` for every real Lie vector X and coefficient
vector v. The conditional result neither proves nor assumes that comparison
in the definitions above. Complexification, compact differential insertion,
relative coefficient cohomology, weights and automorphic occurrence remain
separate obligations.

The number field has independent universe uF. Selected embedding labels and
coefficient indices are small and finite; empty indices and rank zero are
allowed. Both orientations of complex places are the existing actual real
algebra maps. All coefficient vectors are retained.
