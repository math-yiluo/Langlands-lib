# Scalar coordinates and the canonical GL₁ Haar measure

This internal derived module uses the scalar matrix and determinant maps as
inverse continuous group isomorphisms in rank one. The full one-by-one matrix
space is homeomorphic to the scalar field, so pulling a matrix test back along
its inverse gives a scalar Schwartz–Bruhat function, including its value at zero.

The scalar group isomorphism preserves the canonical multiplicative Haar
measures exactly. Its inverse image of the integral matrix group is the actual
integral field-unit group: both a unit and its inverse have integral entries.
These compact open groups have mass one by the existing definitions. Uniqueness
of Haar measure with this normalization therefore proves measure preservation.
Consequently all actual complex integrals and integrability assertions transport
along the scalar isomorphism, with no choice of a rescaling constant.

The proof reuses `scalar_determinant_rankOne` from the published rank-one
character reduction and Mathlib's uniqueness of normalized Haar measure.
It asserts neither a Fourier equation nor existence of local factors.
