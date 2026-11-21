# Scalar extension of the symmetric component

`Langlands.GroupScheme.KneserThree.QuatData.exists_isotropic_component_of_representation` compares the two scalar extensions associated with an embedded quadratic field. Over a field containing that quadratic field, a vector of the extended skew-hermitian form whose value is the distinguished pure quaternion gives a nonzero isotropic vector of the extended symmetric component.

Project the tensor over the ground field to the tensor over the quadratic field. The second coordinate comparison identifies the symmetric component on the image with the conjugated second coordinate of the original pairing. That coordinate vanishes for the distinguished pure quaternion. The first coordinate is linear over the quadratic field in the first argument. If the projection of the original vector vanished, the first coordinate of its pairing with every vector would vanish as well. For its self-pairing, this would force the embedded quadratic root to vanish.

This is the comparison used in T. A. Springer's appendix to Kneser, *Lectures on Galois Cohomology of Classical Groups*, Proposition 5.3.2, p. 109 (PDF p. 115).
