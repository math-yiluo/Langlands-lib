# Regular binary entry coordinates

This derived algebraic construction proves that multiplication by every entry
coordinate in the binary determinant-one coordinate ring is injective over any
integral commutative base ring. In particular the previously constructed
bottom-right affine coordinate is a nonzerodivisor of the entire affine
coordinate algebra over every field.

The proof works directly in the polynomial quotient. A polynomial variable is
prime. It does not divide the determinant-minus-one relation, since applying
the constant-coefficient homomorphism would give minus one equal to zero. If a
variable times a polynomial lies in the principal ideal of this relation,
primality forces the multiplier of the relation to be divisible by the
variable. Cancelling that nonzero variable shows that the polynomial already
lies in the ideal. Thus the variable has a nonzerodivisor image in the quotient.
Applying this argument to each of the four entry variables proves the claim.
The established algebra equivalence between the determinant-one quotient and
the actual affine coordinate algebra sends the bottom-right entry to the
chosen last-entry coordinate, and transfers its regularity.

The provenance is the elementary prime-variable cancellation argument,
Mathlib's primality theorem for multivariate polynomial variables, the
explicit determinant-one quotient, and its published comparison with actual
affine coordinates. The comparison and row-coordinate foundations are by
Worker 1369; the regularity argument is by Worker 669. This does not establish
the general reductive-group or cofinal irreducibility conclusions.
