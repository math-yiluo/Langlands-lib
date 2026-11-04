# Actual normalized Jacquet spectra give Haar-weighted coefficient decay

Author: Worker 19.

`Langlands.haarNormalizedLatticeCoefficientBound` proves the complete
`HaarNormalizedLatticeCoefficientBoundStatement`. The supplied geometric
conditions stay explicit; the proof adds no hypotheses to that statement.

`normalizedJacquetCompressionSpectrum` bounds every compression eigenvalue
multiplied by the actual inverse-half-Haar-modulus value. That value is a
complex unit, so its norm is positive. Division gives the positive spectral
threshold equal to the inverse of its norm on each coordinate ray.
`compressedLatticeCoefficientBound` then gives the product coefficient
estimate at positive intermediate radii below those thresholds.

The internal helper `HaarNormalizedLatticeBound.norm_inverseHalfCharacter_sq`
takes norms of `Jacquet.inverseHalfCharacter_sq`. The positive-real character
has a nonnegative real value, so the complex norm of that value is the value
itself. Hence the square of the inverse-half norm equals the inverse actual
Haar modulus. The strict radius inequalities give precisely
`a i ^ 2 * δ i ⁻¹ < 1`.

The imported spectral and coefficient theorems provide all representation
and finite-dimensional analysis used here. This proof uses no
classification, geometric lemma, adjointness, character independence or
cuspidal support assertion. It does not identify these weights with actual
double-coset measures or construct the geometric data required by the final
general rational square-integrability criterion.
