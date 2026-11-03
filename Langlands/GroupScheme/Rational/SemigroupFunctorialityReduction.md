# Semigroup functoriality from pointed images and coordinate containment

This derived reduction concerns the functoriality paragraph after Example 3.3.7
of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
printed p.111 / PDF p.137. It keeps the two unproved source obligations,
`PointedImageGenerationStatement` and `AugmentationLieContainmentStatement`,
explicit. It does not assert either obligation or the unconditional comparison
theorem. `SemigroupImageTransportPrerequisites` names their conjunction.

The implemented proof works generator by generator for the actual all-test
semigroup subgroup functor. A smooth connected invariant closed source
subgroup has its action restricted to a representing group. Its intrinsic
weight support is the support of that whole representing group, by the
monomorphic action-weight transport theorem. The representative is affine,
and the published smooth-connected geometry theorem makes it geometrically
integral over the field.

Apply the assumed pointed-image generation theorem to its composite into the
target, pointed by the group identity. This gives a smooth affine
geometrically connected representative of the closed image envelope and a
dominant ordered power. The published envelope-stability theorem restricts
the target torus action to this representative. The actual group
homomorphism from the source subgroup into the envelope is dominant because
its ordered power is dominant. The conditional dominant support transport
then bounds the envelope's Lie weights by the same additive subsemigroup.

The envelope therefore is an admissible target generator, and every original
source point maps into it through the actual factor homomorphism. The least
subgroup property of the testwise generated functor yields the claimed
functoriality. No separability or differential surjectivity is assumed for
the original map, and semigroups containing zero remain allowed. The full
semigroup realization theorem is not a premise.
