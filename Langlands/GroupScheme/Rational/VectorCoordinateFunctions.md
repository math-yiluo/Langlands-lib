# Actual coordinate functions for homogeneous vector actions

This internal development concerns an affine group scheme with natural finite
vector coordinates over an arbitrary field and universe. It constructs the
actual affine coordinate function obtained by evaluating one supplied coordinate
at the universal point. Naturality proves that evaluation at every affine point
recovers that coordinate, and each such function vanishes at the identity.

For `HomogeneousVectorCoordinates`, the original all-test diagonal action gives
the corresponding coefficient-algebra diagonal equation. Consequently each
coordinate function is an eigenfunction of its supplied actual character.
Every coordinate block is stable under the original action on every test scheme.

If a coordinate function pulls back to zero along an affine group homomorphism,
its coordinate vanishes on the image on every test scheme. The proof first uses
the universal affine point and the global-sections isomorphism and then pulls
the equality back along an arbitrary point using coordinate naturality.

For both upper-containment results, assume additionally that the acting
commutative group scheme `S` is a split torus and that
`CoordinateWeights.AugmentationLieContainmentStatement` holds. The supplied
`HomogeneousVectorCoordinates` data alone do not imply splitness. Under these
two hypotheses, each smooth connected invariant semigroup generator is contained
in the coordinate block whose labels lie in that semigroup. The representing inclusion transports its
intrinsic Lie support to the full support of the representing group. The stated
comparison bounds its actual augmentation support. A coordinate function whose
label is outside the semigroup therefore restricts to zero; its all-test
vanishing proves containment. The universal property of the subgroup generated
by these generators proves the same upper bound for `semigroupSubgroup`.

The containment theorem is an explicit hypothesis here. This module does not
prove the reverse coordinate-block inclusion, identify the full actual Lie
support with the labels, or prove the full ordered semigroup product theorem.
Empty coordinate sets and semigroups, and zero and repeated labels, are allowed.
