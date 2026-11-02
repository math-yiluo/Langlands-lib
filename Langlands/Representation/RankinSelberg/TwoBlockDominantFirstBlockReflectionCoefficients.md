# Reflected first-block coefficients and the lower slice density

This internal derived calculation supports JPSS, *Rankin–Selberg convolutions*
(1983), Section 4.9, printed pages 416–418 and Section 4.10(2), page 419.
It expands the actual reflected smaller integrand and the actual lower kernel.

The supplied-Haar change of the reflected rectangle contributes the determinant
power minus k. The reciprocal determinant from spectral reflection contributes
minus one. The reflected smaller normalizing power combines with these to give
the inverse half modulus and lower-kernel power, multiplied by the positive
first-block density, the b-th determinant power with b the second block size.
The proof uses only explicit matrix transport, Haar substitution and arithmetic
of determinant exponents. It performs no Fubini exchange and asserts no convergence.

`firstBlockLowerRectangleIntegral` names the actual lower-kernel integral in the
first rectangle at a first-block embedded representative, with the two indices
of the remaining rectangle reversed. The two reflection lemmas identify this
literal integral, first with the determinant-power density and then with the
constant residue-cardinality density on a small determinant slice.

`firstBlockReflectedSmallCoefficient_eq_sliceIntegral` rewrites the actual
reflected smaller coefficient using reflection of its compatible quotient
measure. It exchanges slice minus d with slice d and retains the factor q to
the d. The outer quotient integral remains outside the rectangle integral.
No choice of representatives or exchange of integrals is used.
