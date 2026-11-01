# The local finite-order condition on Harris levels

This module defines the sufficiently small condition of Harris–Taylor,
Chapter III, section 1, printed p.90 (one-based PDF p.98), on the existing
compact-open levels of the opposite original finite-adelic similitude group.
For a finite place `v` of the rationals, `LevelSmallAt` says that every
finite-order element in the actual image of the subgroup in the local
similitude group is the identity. It tests each subgroup element after
`pointsMap (finiteEvaluation v)`, so the condition concerns the local image,
including elements whose preimages have infinite order. `LevelSufficientlySmall`
existentially quantifies this finite place.

The existing `finiteEvaluation` evaluates the rational finite adele at `v`;
`pointsMap` applies the resulting algebra homomorphism to the tensor algebra
and to its similitude multiplier. The level uses the opposite group, as in
the normalized CM polarized tower. The predicate applies the projection to
`MulOpposite.unop g`, recovering precisely the underlying original local
element. Passing to the opposite group leaves finite order unchanged.

The intrinsic proofs show that the local and existential conditions descend
to subgroup levels. Consequently the actual existing Hecke intersection
`U ∩ g V g⁻¹` is sufficiently small if `U` is. `SmallLevelCategory` is the
full subcategory of the actual transporter category, retaining every original
arrow between these objects. No existence or cofinality of small levels,
representability, or finite étaleness theorem is asserted here.

The original source is Harris and Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The finite-order predicate is source-backed; the monotonicity and Hecke
proofs are direct consequences implemented here by Worker 57.
