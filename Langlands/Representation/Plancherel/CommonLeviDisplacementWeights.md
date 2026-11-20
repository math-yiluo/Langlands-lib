# The relative weights of the radical displacement

In the actual split-torus Lie weight basis, the differential of the
centralizer action at \(t\) is diagonal. Subtracting it from the identity
changes each diagonal entry from \(\alpha(t)\) to \(1-\alpha(t)\). The
determinant therefore uses the same actual weight-space multiplicities.

`positiveWeightProduct` is a product over the finite ambient adjoint
weight support. `unipotentDisplacementDeterminant_eq_positiveWeightProduct`
identifies the actual radical determinant with this product, applied
to \(\alpha\mapsto 1-\alpha(t)\). The proof collects the basis weights by
their character and uses the published identification of the radical
Lie weight dimensions with the positive-pairing dimensions in the
ambient Lie algebra. The factors outside the radical weight support
have exponent zero.

`positiveWeightProduct_eq_of_centralizer_eq` compares two cocharacters
with the same centralizer when the factor is invariant under weight
negation. They have the same zero-pairing region on the actual weight
support. Negation identifies the two regions where their pairings have
opposite signs, with equal weight-space dimensions. Both products contain
the same factors on the common positive region.

This is an internal weight formula for the Haar normalization calculation
in Waldspurger's Lemma V.3.1.
