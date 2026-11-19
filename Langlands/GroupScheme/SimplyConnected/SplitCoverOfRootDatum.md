# Split simply connected covers from root-datum existence

Worker 169, Task 7298. Helper module of `IndependentHaboushReduction`. It contains no
proof of geometric reductivity or of root-datum existence.

## Statement

`splitSimplyConnectedCoverExistence_of_rootDatumExistence` is a conditional implication.
It assumes the published proposition `RootDatumExistenceStatement.{u}` and concludes
the published proposition `SplitSimplyConnectedCoverExistenceStatement.{u}`, at every
universe `u`. The conclusion says: for every field `k`, every semisimple group `G` over
`Spec k` and every split maximal torus `i : T ⟶ G`, there is a central isogeny
`π : C ⟶ G` from an algebraically simply connected group `C` (the split case of
Milne, *Algebraic Groups*, Remark 23.60). The theorem adds only the root-datum premise.
It does not change the conclusion's quantifiers, field generality or universe.

## Proof

The proof applies the published conditional reduction
`splitSimplyConnectedCoverExistence_of_minimalLattice` from
`SimplyConnected/SplitCoverMinimalLattice.lean`. That reduction takes three inputs:
root-datum existence, the root-datum morphism of a central isogeny
(`CentralIsogenyRootDatumHomStatement`), and perfectness of semisimple groups
(`SemisimplePerfectStatement`). Among the central covers of `G` with a split maximal
torus over `i`, it chooses one whose coweight image has minimal index over the coroot
span, and shows that this cover is simply connected. Here the root-datum input is the
hypothesis, and the Library theorems `centralIsogenyRootDatumHom` and
`semisimplePerfect` supply the other two inputs.

The published unconditional `splitSimplyConnectedCoverExistence` makes the same call
with `rootDatumExistence` as its first argument. That argument is the only point where
it depends on the excluded rank-one input:
`rootDatumExistence → rootDatumExistence_of_splitWeylRationality → rootReducedness →
RootReducedness.rankOneRootReducedness → RankOnePositiveRootUniquenessStatement`.
This module turns that argument into a premise. `IndependentGeometricReductivityProof`
supplies it from the rank-one central cover, through Task 7458's reducedness theorem.

## Dependency audit

A full type-and-value closure audit was run on 17 November 2026 (private diagnostic
`67e07da0-f706-4b94-b7de-feb9cf64f46a`, with a private scanner). For every reached constant, the scanner follows every constant in its type
and in its value, including opaque proof values and instances. It reached 19,815
`Langlands` constants and none of the following excluded names:
`ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`,
`RankOnePositiveRootUniquenessStatement` and their proofs `parabolicDynamic`,
`regularCocharacterBorel`, `rankOneSolvableObstruction`, `rankOneBorelDynamic`,
`rankOnePositiveRootUniqueness`. `centralIsogenyRootDatumHom`, `semisimplePerfect` and
`splitSimplyConnectedCoverExistence_of_minimalLattice` are each clean under the same
audit. As positive controls, the scanner finds the excluded statement in the closures of
`rootDatumExistence`, `splitSimplyConnectedCoverExistence` and the current
`HaboushReduction.exists_simplyConnected_cover_of_isSemisimple`.

A compiler diagnostic does not establish independent semantic acceptance.
