# Cancellation of the actual central matrix denominators

This internal algebraic consequence combines the published shifted determinant
weights with the reciprocal geometric cancellation and rational monomial
functional-equation helpers. It does not assert a functional equation exists.

For a matrix `z` of rank `n+1` and a scalar `omega`, the definition
`matrixGeometricCoefficient` is `alpha = omega * |det z|^(n/2)`. It is the
parameter in
`matrixGeometricDenominator = 1 - C(alpha) * T(ord(det z))`.

For a unit `omega`, the product of this coefficient with the reflected dual
coefficient is `|det z|^(n+1)`. Indeed, the two central-character scalars cancel,
and reciprocal spectral substitution contributes
`q^(-ord(det z)) = |det z|`. The Lean proof uses the existing shifted spectral
weight identity at parameter one and the addition law for complex powers of a
nonzero positive real. If `|det z| < 1`, this product is different from one.
The argument works for every positive matrix rank.

The final theorem assumes actual rational functions with Laurent numerators
after multiplication by the respective original and dual central geometric
denominators. It also assumes the guarded normalized functional equation with
both polynomial factors one and a nonzero Laurent monomial multiplier. The
rational-identity helper converts that equation to reciprocal substitution.
The coefficient inequality then permits the explicit Bezout cancellation from
`exists_laurent_of_reflected_geometric_clearings`, producing a Laurent preimage
of the original rational function.

All assertions are derived from the existing concrete Laurent and rational
function rings and normalized determinant weights. No representation-theoretic
existence result is assumed beyond the displayed inputs, and no original
literature is cited for this internal specialization.
