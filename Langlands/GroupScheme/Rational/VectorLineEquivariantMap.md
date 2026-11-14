# Actual equivariant vector-line maps

This internal derived module converts equivariance of an actual homomorphism
between naturally coordinated vector lines into the universal polynomial
identity in the actual torus coordinate algebra. The action and the natural
coordinates are required on every scheme test. It also proves that an actual
map which is an epimorphism on the underlying relative schemes has nonzero
polynomial, using an affine presentation of the source.

The scalar action formula is the supplied weight-coordinate equality on affine
tests. Naturality of the map polynomial identifies the image coordinate, and
actual equivariance gives its transformed value. Apply that equality to the
universal torus point extended to O(T)[X] and to the vector point with coordinate
X. Naturality of character evaluation gives the desired universal equation.

For nonvanishing, a zero polynomial would make every affine point map to the
identity. Evaluating at the source's affine universal point makes the map
constant. Epimorphic cancellation would then make the target identity morphism
constant, contradicting its point with scalar coordinate one over the field.

When the torus is split and the source character is nonzero, `powerMonomial`
combines these results with the additive-polynomial classification. It chooses
a unit scalar and a natural number r, proving that the actual map polynomial
is that scalar times X to the power (ringExpChar k)^r, and that the target
character equals (ringExpChar k)^r times the source character in the actual
integral character lattice. No perfectness or separability is required.

Provenance: derived from the Library's natural vector coordinates, actual
affine presentations, universal character-unit embedding and pointwise
character evaluation, together with the internal characteristic-power
classification in `IsogenyRootPolynomial`. This module does not yet identify
any character as a root or prove the full isogeny comparison.
