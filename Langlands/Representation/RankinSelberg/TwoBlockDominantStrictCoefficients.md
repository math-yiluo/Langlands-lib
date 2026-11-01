# Actual strictly dominant coefficient support

This internal unit names the actual fixed-rank unequal-rank determinant
coefficients and derives their finite negative tail from the published smooth
simple-root support and determinant bound. It asserts no convergence or
first-block functional equation.

The supplied scalar additive Haar measure is used through its exact nested
rectangle product; `strictRectangleMeasure` changes only the displayed
measurable-space structure to the canonical Borel space.
`strictSliceCoefficient` transports the test along
`r = n + (j + k + 1)` before applying the existing coefficient definition at
parameter zero.

For the support proof, smoothness of the larger representation gives a positive
bound on the adjacent Iwasawa diagonal ratios wherever its Whittaker coefficient
is nonzero. The actual unequal-rank matrix has last row the last standard row
and determinant equal to that of the smaller matrix. The imported determinant
bound with row bound one therefore bounds that smaller determinant's absolute
value. Since the residue cardinality exceeds one, a sufficiently negative
determinant order contradicts this bound. The Whittaker coefficient then
vanishes pointwise throughout both integrals, so the slice coefficient is zero.
No integrability, compatible quotient measure, nonzero functional, full
Whittaker type, or condition on the smaller Whittaker function is used.

This is an internal deduction from existing Library proofs. It neither changes
the final dominant-rank statements nor establishes a gamma or L comparison.
