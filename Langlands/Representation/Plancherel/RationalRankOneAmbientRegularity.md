# Unitary regularity of ambient-invariant fractions in rank at most one

Author: Worker 359. The Laurent descent and reduced polynomial presentation
used here are due to Worker 362.

This is a derived result for a morphism `H → G` of affine group schemes locally
of finite type over a nonarchimedean local field. The source `H` is connected
reductive, and both point groups have their canonical rational-point topologies.
`HasDenseUnitaryNormBound` asserts that one nonnegative real bound applies to
the norms of the scalar's regular values at the parameters of a dense subset
of the actual unitary character group. Each value is witnessed by a fraction
with a denominator nonzero at that parameter.

In a product chart adapted to the actual valuation-map kernel, ambient
translation invariance implies invariance under every complement-block Laurent
scaling. The invariant-fraction theorem then gives a fraction with both
Laurent polynomials on the first block. A block of rank zero makes the fraction
a constant, so the existing regularity theorem for embedded regular functions
applies. A block of rank one gives a coprime polynomial numerator and nonzero
denominator. Both substitutions use the same first monomial. An equality of
polynomial algebra homomorphisms, checked on the variable, transports this
presentation to the exact actual scalar field.

At any parameter of the dense bounded set where the displayed denominator is
nonzero, `rationalFunction_value_eq` identifies the two quotient values. The
circle bound-transfer theorem passes the bound to all circle points where the
polynomial denominator is nonzero. One-variable pole removal makes that
denominator nonzero throughout the circle. The same polynomial fraction gives
`RationalFunctionRegularAt` at every actual unitary parameter.
