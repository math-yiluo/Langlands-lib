# Integrating natural additive two-cocycles

Worker 1485. This internal derived unit applies the published scalar polynomial
cocycle theorem to a natural family over all coefficient algebras.

A `ScalarFamily` assigns a scalar `c_A(x,y)` to each pair of elements of every
commutative algebra over the field. `IsNatural` requires compatibility with
every algebra homomorphism, and `IsCocycle` requires the ordinary additive
two-cocycle identity. No normalization or symmetry hypothesis is imposed.

Naturality identifies the family with the evaluation of its value at the
universal pair `X,Y` in the bivariate polynomial algebra. The cocycle identity
on the trivariate polynomial algebra gives the actual polynomial cocycle
identity. The value at `(x,0)` is constant by cancellation in the cocycle
identity, so the coefficient of degree zero in the second variable is the
constant value at the origin. Subtracting that constant normalizes the
polynomial. The existing
`Unipotent.OneDimensional.exists_eq_coboundary_of_charZero` integrates this
normalized polynomial in characteristic zero; adjusting its primitive by a
constant recovers the original family.

`coboundaryPolynomial` selects such a primitive, and its specification holds
over every coefficient algebra. This is an algebraic consequence of the
existing theorem and polynomial universal properties, with no additional
classification or external source input.
