# A unitary coordinate on the primitive rank-one valuation kernel

This derived unit works over a nonarchimedean local field with an affine
parameter group scheme locally of finite type. Its supplied integral product
chart has a first block indexed by `Fin 1`. In the chart adapted to an
ambient valuation map, this first block is the rank-one kernel.
The `firstGenerator` is the actual primitive valuation element corresponding
to that coordinate.

`firstUnitaryCoordinate` evaluates the descended circle-valued character of an
actual unitary unramified parameter at this element. It is continuous and
surjective. Surjectivity is proved by constructing the circle character that
raises a prescribed circle point to the first integral coordinate, then
reconstructing the corresponding actual unitary parameter.

`firstRegularCoordinate` is the exact Laurent monomial in the existing actual
regular scalar algebra. Its unitary values agree with `firstUnitaryCoordinate`.
`firstPolynomialMap` substitutes this regular monomial into a complex
polynomial, with the corresponding exact evaluation identities.

For a connected reductive parameter group, `regularAt_of_firstPolynomialFraction` supplies the original
`RationalFunctionRegularAt` presentation whenever the scalar has a displayed
polynomial-fraction expression in this coordinate and its denominator is
nonzero at the chosen unitary value. The substituted numerator and denominator
are the witnesses for the algebraic definition.

`circle_quotient_bound_of_dense` is a general topological bound-transfer
lemma. At each circle point where the displayed denominator is nonzero,
the polynomial quotient is continuous at a preimage. Its bounded values
on a dense set then lie in the same closed norm ball at that preimage.
At zero denominator, the total quotient is zero, which suffices to handle
those dense-set points in this argument.
`firstPolynomialFraction_circle_bound_of_dense` specializes this to the actual
unitary coordinate and gives the bound at every circle point where the
displayed denominator is nonzero.
