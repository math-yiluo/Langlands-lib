# Action weights under equivariant subgroup inclusions

This internal transport module uses the actual dual-number identity kernels,
epsilon scaling, and intrinsic action eigenvector constructions. It is derived
from postcomposition of scheme maps and uses no additional literature result.

The published `Lie.targetMap` from `Rational.SplitTorusFiniteRank` is postcomposition on the actual kernel of reduction. Its linear form is the published `Lie.targetMapLinear`;
linearity follows from compatibility with the kernel group law and epsilon
scaling. Coefficient change and scaling commute with this map by associativity
of scheme composition. A monomorphism induces an injective kernel map. If an ambient kernel vector
lies in the image of a subgroup, any point lifting it is itself in the identity
kernel: cancellation after reduction proves this without requiring smoothness.

For an equivariant monomorphism between affine group schemes, the intrinsic
action eigenvector condition is preserved and reflected: equivariance rewrites
the action equation, and cancellation by the monomorphism reflects equality.
The weight-space result uses the published identification of the eigenvector
set with its linear span. `actionWeightSupport_map` combines this equivalence
with lifting in the actual reduction kernel and injectivity of the induced
linear map. Thus all support characters, including a possible zero character,
are preserved and reflected for the image of any all-test subgroup.

These lemmas are transport helpers; they do not prove the Dynamic ordered-root
product target or supply its required realizations.
