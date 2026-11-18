# A uniform bound for an inverse continued composite scalar

This is an internal consequence of the published rational continuation and
continued adjunction constructions, together with
`InverseQuadraticCoefficientBound`. It has no external source attribution.

`RationalFunctionNormBoundedAt` means that a rational function has a fraction
presentation whose denominator does not vanish at the specified parameter and
whose complex value has norm at most the specified real bound. In particular it
implies `RationalFunctionRegularAt` there.

The theorem `exists_continuedCompositeRationalScalar_inv_norm_bound` concerns two
independently continued linear operator families. Their forms satisfy adjunction
on an open nonempty subset of the first family's original region, and
conjugate-inversion carries that subset into the second original region. The
target form comes from a positive definite Hermitian core. On the fixed
extracting vector, the source form has nonzero diagonal. A fixed linear
functional of the continued forward vector must have a constant nonzero value
throughout its regular region.

The theorem gives a single positive bound for the inverse extracted rational
scalar at every self-dual common regular parameter. The coefficient's fraction
value is the target quadratic coefficient divided by the fixed source
diagonal, by continued adjunction. The constant detecting functional makes the
target quadratic coefficient nonzero and bounds its reciprocal uniformly, using
the finite span of the polynomial numerator. Swapping numerator and denominator
then witnesses the inverse scalar's regularity and bound at those parameters.
No parameter compactness, finite dimension of either ambient carrier, generic
scalarity of the composite, or positivity of the source form is assumed.

The parameter group is a connected reductive group scheme over any
nonarchimedean local field, with a continuous rational valuation projection.
The field, source carrier and target carrier have independent universes.
The result only concerns self-dual common regular parameters; it makes no
assertion of algebraic regularity at other points.
