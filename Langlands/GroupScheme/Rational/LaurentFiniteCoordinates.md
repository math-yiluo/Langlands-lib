# Finite primitive-orbit coordinates of pointed Laurent functions

This internal construction restricts the polynomial encoding in
`LaurentAdditiveCoordinates` to finitely many primitive characters.
For any commutative ring `k`, prime `p`, and arbitrary index type `I`,
`finiteOrbitSpace s` is the linear span of the Laurent coefficient basis
vectors `X^((p^r) • a) - 1`, with `a` in the finite set `s` and arbitrary
natural `r`. In characteristic `p` these vectors also equal
`(X^a - 1)^(p^r)`. The coefficient and index universes are independent.

`finiteProjection` sends a variable indexed by a member of `s` to its
variable in `Fin s.card`, and sends every other variable to zero.
Composing with the full linear encoding gives `finiteEncoding`.
Renaming the finite variables back to the primitive characters recovers
the full encoding on `finiteOrbitSpace s`. Since the full encoding is
injective, the finite encoding is injective on this subspace.

The coefficient representation of each Laurent function has finite
support. The union of its primitive-character projections for a finite
family therefore gives a single `s` containing that family in
`finiteOrbitSpace s`.

In characteristic `p`, each such subspace is Frobenius-stable: Frobenius
advances the second basis index and leaves its primitive character fixed.
The finite encoding commutes with Frobenius because the full encoding
does and the finite projection is an algebra homomorphism. Each encoded
basis vector is either a power `Y_j^(p^r)` or zero. Expanding in the
coefficient basis then proves that every finite encoding is additive
on every commutative algebra in the sense of `TorusLinearization.IsAddPoly`.

This is a direct finite-support and basis argument. It does not assert
that the entire additive-function module of an algebraic group has finite
primitive-orbit support, or classify any group scheme.
