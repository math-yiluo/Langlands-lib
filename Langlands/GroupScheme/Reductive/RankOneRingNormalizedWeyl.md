# The normalized Weyl product from the ring rank-one relation

This internally derived construction applies the arbitrary-ring rank-one
relation to the three-factor product formed from the supplied unit beta
coordinate. For every test the product is the negative-root point at minus
beta, the positive-root point at one, and the same negative-root point.
The group scheme is assumed affine for use of the ring relation.

Applying that relation with first coordinate one and second coordinate
`q - 1` gives the rescaling identity for every unit `q`. Torus equivariance
then shows that conjugation by the normalized product acts on the torus
through the actual root-coroot reflection. The argument holds on all scheme
tests over the commutative base ring, so retains its nilpotent structure.
Naturality identifies the product with the restriction of its base section;
point extensionality gives an actual `IsNormalizingPoint` proof.
