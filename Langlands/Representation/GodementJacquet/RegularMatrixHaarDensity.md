# Cancellation of the matrix determinant density

This internal helper derives an integral formula from the published
determinant-density construction of GL Haar measure. It assumes no
functional equation.

`matrixDeterminantPower r χ X` abbreviates the existing
`GLDeterminantDensity.forwardWeight r χ X`, the nonnegative number `χ(det X)^r`.
On invertible matrices it is the reciprocal of the density used by
`weightedRestriction`. For a complex function vanishing on all singular
matrices, the weighted GL integral of this power times the function is its
full additive matrix integral. The proof first applies the existing
weighted-restriction formula, cancels the nonzero determinant power on the
invertible locus, and then removes the restriction using the stated
vanishing. It requires no assertion that the singular locus has measure zero.

For every canonical p-adic realization, matrix size `n+1`, and supplied scalar
additive Haar measure, uniqueness of GL Haar supplies one positive finite
scalar `c`, independent of the function. The resulting equality is

`c * ∫GL f(g) |det g|^(n+1) dg = ∫Matrices f(X) dX`.

The group measure is the actual canonical normalized GL Haar measure and the
additive measure is exactly the square product of the supplied scalar measure.
The positive determinant power is identified with the Library's actual complex
power at the natural integer exponent. The formula uses the total Bochner
integral convention and does not assert integrability of arbitrary functions.
