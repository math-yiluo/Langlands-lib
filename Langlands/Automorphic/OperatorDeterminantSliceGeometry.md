# Determinant slices of the actual general-linear rational quotient

This is an internal construction for the actual local unitarity proof. All
objects and elementary facts are derived from the imported Library results;
there is no new literature translation. The group scheme is the existing
matrix general-linear group, and the quotient is its existing principal
rational quotient. The published adelic matrix homeomorphism identifies its
points with the original adelic general-linear group.

`groupDeterminantNorm` transports the actual adelic determinant norm through
that homeomorphism. Its rational value is one by the published product formula,
so `quotientDeterminantNorm` descends it continuously to the rational quotient.
The open band `band` is defined by the strict inequalities
\(1<|\det|<2\). Right translation multiplies the quotient determinant norm by
the norm of the translating element. Consequently norm-one right translations
preserve the band, and any quotient measure preserved by such a translation
retains that property after restriction to the band. The measure remains an
explicit parameter; the file proves no right-invariance or volume theorem for
an actual Haar measure.

For positive rank, `exists_scalar_determinantNorm` constructs a scalar idele
with any prescribed positive determinant norm. The positive real idele with
parameter the \(1/([F:\mathbb Q]n)\)-power of that norm has the required
value by `PositiveRealIdeles.absoluteValue_full`. The denominator is nonzero
because the number-field degree and rank are positive. The resulting
`exists_normalized_rightTranslate` centrally corrects any matrix translate
to have determinant norm one.

Finally, `toQuotient` maps the original `OperatorRealization.Space` linearly
into continuous functions on this quotient, using the two published function
comparison equivalences and `OperatorRealization.toContinuous`. Evaluation on
a represented coset is exactly evaluation of the original function on the
corresponding adelic matrix. The map is injective because each comparison is
injective. No central character, boundedness, integrability, positive form or
local unitarity is asserted here. These facts provide the geometry and the
unchanged function carrier needed for the subsequent integral construction.
