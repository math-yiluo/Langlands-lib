# Coordinates of the binary triangular special linear group

For every commutative base ring `R`, the coordinate algebra of the actual
upper-triangular subgroup of the binary special linear group is the
polynomial ring `R[b,d]` with `d` inverted. `Coordinates.quotEquiv` is an
explicit equivalence of `R`-algebras from the published subgroup's quotient
coordinate ring to that localization.

The generic determinant-one matrix in these coordinates is
`[[d⁻¹,b],[0,d]]`. Its classifying map kills the lower-entry ideal and so
descends to the actual triangular coordinate ring. In the reverse direction
the variables specialize to the universal upper-right and last-diagonal
entries. The last entry is a unit: the determinant-one equation and the
vanishing lower entry identify its inverse with the first diagonal entry.
The localization's universal property therefore extends the specialization.
Entrywise comparison of the universal matrices proves one composite is the
identity; comparison on the two polynomial variables and localization
extensionality prove the other.

The equivalence proves that the actual triangular group is smooth over
every commutative base ring, since polynomial algebras and localization at
one element are smooth. Over a domain the localized polynomial ring is a
domain, because the inverted variable is nonzero. Consequently the actual
triangular scheme is irreducible and connected.

This is an internal coordinate calculation using the published
determinant-one coordinates and triangular entry ideal, together with
Mathlib's polynomial, localization, smoothness and spectrum results.
It does not establish Borel maximality, parabolicity, or the general local
Kneser–Tits theorem.
