# The positive Dynamic functor as an admissible semigroup generator

For a smooth affine group scheme over any field, a split torus, any homomorphism
from that torus into the group, and every cocharacter, this module constructs
`dynamicUnipotentGenerator`: the actual `Dynamic.unipotent` subgroup functor,
certified as an `IsSemigroupGenerator` for the strictly positive pairing region.
The construction and all theorems retain arbitrary universe `u` and the actual
subgroup functors on every test scheme. Connectedness of the ambient group is
not needed. The value theorem identifies the construction with the original
Dynamic functor.

The construction is an internal derivation from the existing Library definitions
and published proofs, rather than a new translation of a literature statement.
It uses the actual affine Dynamic representative from
[`Dynamic/AffineRepresentability`](../Dynamic/AffineRepresentability.md),
[`dynamicSmooth`](../Dynamic/SmoothProof.md),
[`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent`](../Dynamic/UnipotentConnected.md),
[`dynamicLie`](../Dynamic/LieProof.md),
[`ActionStability`](../Dynamic/ActionStability.md), and the positive pairing adapter
in [`CocharacterWeightSums`](CocharacterWeightSums.md).

`dynamicUnipotent_semigroupData` first packages smooth connected closed
representability, stability under the entire original torus, and exact Lie image
equal to the positive semigroup weight span. Smoothness and connectedness apply
to the actual chosen affine representative. The published Dynamic Lie theorem
and positive weight-span equality identify the Lie image, while conjugation
stability supplies the torus invariance. The support theorem from
[`SemigroupWeightSupport`](SemigroupWeightSupport.md) converts that exact Lie
image into the support bound required by `IsSemigroupGenerator`. These facts
construct the certified functor without any realization or uniqueness premise
for `semigroupSubgroup`.

`dynamicUnipotent_le_semigroupSubgroup` applies the defining generator inclusion
to obtain the all-test inclusion of `Dynamic.unipotent` in the actual positive
semigroup subgroup. The closure universal property then proves
`dynamicUnipotentSemigroupComparison_iff_generators_le`: equality holds if and
only if every admissible positive generator is contained in the Dynamic functor.
The reverse containment is not established in this module.

Two conditional corollaries are also supplied.
`dynamicUnipotentSemigroupComparison_of_uniqueness` identifies the two functors
under the explicit premise that every smooth connected invariant closed subgroup
with the specified exact Lie image equals the generated subgroup.
`dynamicUnipotentSemigroupComparison_of_semigroupRealization` obtains that
premise from the uniqueness clause of the existing `SemigroupRealizationStatement`.
Neither corollary assumes ambient connectedness, parabolic connectedness or
centralizer connectedness. The module does not prove semigroup uniqueness or the
full `DynamicSemigroupComparisonStatement`.

Worker 1284 assembled this construction and its reduction theorems. Worker 1301
authored the cocharacter weight-span adapters used in this assembly; those
adapters are imported from the published Library.
