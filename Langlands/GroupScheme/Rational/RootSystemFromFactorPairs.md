# Relative root systems from opposite factor pairs

This internal supporting unit proves that opposite-factor-pair existence for a
maximal split torus in a connected reductive group supplies the existing
`HasRelativeRootSystem` predicate. It also derives the exact global
`RelativeRootSystemStatement` from the exact global
`RootRankOneFactorizationStatement`. The latter remains an
explicit premise. This unit does not construct opposite factor pairs or prove
`RootGeneratedCentralizerRankOneStatement`.

All fields and group schemes lie in an arbitrary universe. There are no
perfectness, characteristic, reduced-root-system or nonemptiness restrictions.
The pointwise theorem assumes the documented affineness and monomorphism
instances; the global theorems obtain them from reductivity and maximal
splitness.

## Implemented proof

For fixed actual reductive data, the published
`RelativeRootReflectionData.ofOppositeFactorPairs` chooses an actual
normalizing triple in each opposite-root generated subgroup. It supplies
integral cocharacters pairing to two and the lattice reflection formulas.
Smoothness comes from reductivity, and splitness comes from the maximal split
torus. The published finite-root theorem gives finiteness of the actual root
set, and the generic-cocharacter theorem supplies a generic cocharacter,
including when the root set is empty.

The published `hasTrivialPositiveRootStabilizer` proves that the positive-root
stabilizer of this cocharacter is trivial. Its proof uses integral averaging
and the generic-centralizer theorem, with no root-system or reflection
existence premise. Applying
`RelativeRootReflectionData.hasRelativeRootSystem_of_positive_stabilizer`
therefore constructs the evaluation root pairing, identifies its root range
and Weyl image, and proves faithfulness of the actual Weyl quotient on the
actual root span.

For the global reductions, the existence part of the supplied rank-one
predicate gives `HasOppositeFactorPairs` at every field and maximal split torus.
The pointwise result gives `RelativeRootSystemStatement`. The proposition
`RootRankOneRootSystemReductionStatement` records this implication, and
`rootRankOneRootSystemReduction` proves it.

## Provenance and scope

This is an internal composition of the published opposite-pair representative,
finite-root, generic-cocharacter, positive-stabilizer and chamber-generation
results. It adds no literature assertion and cites no classical
relative-root-system construction in place of those proofs. Its remaining
structural premise is opposite-pair existence, or globally the full rank-one
factorization statement; it establishes neither premise unconditionally.
