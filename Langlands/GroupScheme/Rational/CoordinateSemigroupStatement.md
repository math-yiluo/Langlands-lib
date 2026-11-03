# Positive augmentation-weight semigroup comparison: targets

`AugmentationLieSemigroupStatement` states Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), Example 3.3.2, printed p.108 /
PDF p.134, for the Library's actual coordinate augmentation and original actual
Lie-kernel support. This is an unproved `Prop` definition.

For a smooth connected affine group over an arbitrary field, acted on by an
actual split torus, the target equates `CoordinateWeights.support b` with the
set underlying `AddSubsemigroup.closure (RelativeRoot.actionWeightSupport b ⊤)`.
The left side is the support of nonzero augmentation eigenfunctions, not the
closure of a support by definition. The right side consists of positive finite
sums of intrinsic Lie weights. An empty Lie support therefore generates the
empty additive subsemigroup. The zero character is never inserted as an empty
sum, but is allowed when it occurs or is a positive sum of occurring characters.

The printed proof uses that the smooth connected group is geometrically integral,
so products of nonzero eigenfunctions are nonzero. It compares the augmentation
to its cotangent, passes to the identity local ring, uses the separated maximal-
ideal filtration and the equivariant tensor-power surjections onto its graded
pieces. Those are mathematical proof obligations, not assumptions supplied by
this target. The cotangent/Lie support comparison is stated separately in
`CoordinateLieComparisonStatement`; the present target retains the original
`RelativeRoot.actionWeightSupport` rather than replacing it by a coordinate
surrogate. All field characteristics, including positive characteristic, remain.

`AugmentationLieContainmentStatement` records the equivalent criterion for every
additive subsemigroup `M`: augmentation support lies in `M` if and only if the
intrinsic Lie support lies in `M`. It includes the empty semigroup and makes no
assumption that `M` contains zero. Deriving it from the equality uses the universal
property of positive semigroup closure. Conversely, applying the criterion to
the closure and using that augmentation support is a semigroup recovers the
source equality; that closure fact is part of the source proof route and is not
claimed here without proof.

`CoordinateSemigroupComparisonStatement` is their conjunction. These targets
serve semigroup realization and the commutator bound without assuming either
consumer conclusion. Their focused proof successor must discharge the source
arguments; publishing this statement module does not prove Example 3.3.2.
