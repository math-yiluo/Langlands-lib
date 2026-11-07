# The relative Tits system from two geometric statements

This internal supporting unit reduces the existing exact
`RelativeTitsSystemStatement.{u}` to `RationalBruhatStatement.{u}` and
`RootRankOneFactorizationStatement.{u}`. The proposition
`RelativeTitsGeometricPremises` is precisely their conjunction. Both statements
remain premises; this unit does not prove the unconditional Tits target.

A second reduction replaces the rank-one premise by
`RelativeRoot.KernelCentralizerComponentReductiveStatement.{u}`, retaining
rational Bruhat decomposition. This gives a route through actual full
scheme-theoretic character-kernel centralizers. It does not prove their
component reductivity or rational Bruhat decomposition.

Every statement has arbitrary universe `u` and arbitrary field scope. The
conclusions use the unchanged actual group schemes, maximal split tori,
relative roots, rational normalizers and centralizers, and generic
cocharacters. Rank zero and nonreduced relative root systems are included.
No perfectness, characteristic, positive-rank or splitness condition on the
ambient reductive group is added.

## Implemented proof

`relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization` first applies
[`relativeRootSystemStatement_of_rootRankOneFactorizationStatement`](RootSystemFromFactorPairs.md).
That published implication constructs integral reflections from actual
opposite factor pairs and uses the unconditional positive-root stabilizer
averaging theorem to obtain the full relative root system, including
faithfulness of the actual Weyl quotient.

The assumed rank-one statement and the derived root-system statement form
`RootGeneratedCentralizerStructuralPremises`.
Its published `relativeWeylCoxeter` theorem supplies integral reflection
representatives centralizing the full character kernels and applies the
unconditional abstract root-pairing Coxeter theorem. Its published
`dynamicRootOrderedProduct` theorem derives actual root-ray decomposition
and applies the arbitrary-field unipotent ordered-product theorem. These
are deductions from the two supplied statements, rather than additional
premises.

The published [`relativeTitsSystemStatement_of_coreStatements`](RelativeTitsCoreAssembly.md)
then applies with those derived inputs, the assumed rational Bruhat and
rank-one statements, and the unconditional exact proofs
`standardParabolicEndpoints` and `genericCentralizer`. The core assembly
supplies nondegeneracy from actual nonidentity simple-root points. Thus its
conclusion retains all three parts of `HasRelativeTitsSystem`, including
uniqueness of simple-root reflections and injectivity of their indexing.
`RelativeTitsGeometricPremises.relativeTitsSystemStatement` is the same
implication with the two premises bundled.

`relativeTitsSystemStatement_of_bruhat_and_kernelCentralizerComponentReductivity`
introduces an arbitrary connected reductive group and maximal split torus.
Reductivity supplies affineness and smoothness; maximal splitness supplies
the torus monomorphism and splitness. The published
[`exists_oppositeFactorPair_of_bruhat_and_componentReductivity`](RootFactorPairExistenceReduction.md)
provides an actual opposite pair for each nonidentity actual root point,
using the assumed Bruhat and component-reductivity statements. The published
[`hasRankOneFactorization_of_hasOppositeFactorPairs`](RootFactorizationFromExistence.md)
gives the entire rank-one predicate, including uniqueness over all
normalizing opposite pairs, reflection behavior, and the nonmultipliable
consequences. Applying the preceding two-input reduction proves the
conditional Tits conclusion.

## Provenance and remaining obligations

Worker 1288 composed these published implications after Worker 1225
identified the averaging and factor-pair route that avoids parabolic
classification as an input to root-system existence. The mathematical
provenance is internal composition of the linked Library results and
[`RootGeneratedCentralizerReduction`](RootGeneratedCentralizerReduction.md).
No new external structural assertion or axiom is introduced.

Acceptance of this unit establishes only the stated conditional implications.
An unconditional proof of either remaining geometric input must be
independent of the downstream Tits and classification targets before these
reductions can complete the host proof task.
