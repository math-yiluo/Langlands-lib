# Additive polynomial points and vector-group homomorphisms

This internal construction identifies an actual point over the polynomial ring
in `n` variables with its underlying morphism from the vector group. The
predicate `PolynomialPoint.IsAdditive` is the addition identity on the two
universal tuples in `2n` variables. Substitution proves the identity over every
commutative base-field algebra. In particular, additivity forces the zero tuple
to map to the identity; no additional zero condition is assumed.

The corepresentation of the vector group identifies each affine vector point
with the spectrum map of polynomial evaluation at its coordinates. The generic
identity therefore proves multiplication preservation on affine tests. Affine
extensionality proves the equality on the universal pair of vector points,
and precomposition extends it to arbitrary relative test schemes.
`homOfAdditive` is the resulting actual group-scheme homomorphism, and
`homOfAdditive_hom` identifies its underlying morphism with the original point.

The base is any field in one arbitrary universe. The target group scheme need
not be affine, commutative, smooth, connected or unipotent. These are generic
polynomial and represented-functor arguments; this module asserts no
nontriviality or split-unipotence descent result.
