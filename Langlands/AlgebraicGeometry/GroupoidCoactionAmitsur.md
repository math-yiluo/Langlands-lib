# Comparing induced groupoid cocycles with the Amitsur complex

This internal algebraic comparison is derived from the published induced
coaction formula and the explicit Amitsur differentials. The rings B and C have
arbitrary universe u, and the coefficient module N has independent universe v.
Write A for the published invariantRing t. Assume an explicit B-algebra
equivalence e : B ⊗_A B ≃ C whose second inclusion is the target map t.
Tensor cancellation and associativity identify C ⊗_B (B ⊗_A N) with
B ⊗_A (B ⊗_A N), and identify the corresponding triple-coordinate module
with B ⊗_A (B ⊗_A (B ⊗_A N)). The ring presentation and faithful flatness
are not derived here.

The three pairwise projections of the triple tensor ring supply composable
points. The first edge uses the middle and last factors, the second uses
the first and middle factors, and the third uses the first and last factors.
The target property of e proves their compatibility equations.

Tensor induction proves that the published induced coaction's coboundary
becomes d0 from FaithfullyFlatAmitsurDegreeOne. Under the same tensor
identifications, compose minus third pullback plus second pullback becomes
d1. For a pure coefficient tensor a ⊗ b ⊗ n, the three terms insert 1 in
the first, middle and last positions, with the signs of d1. Additivity
extends the equality to arbitrary tensors. The comparison itself needs no
ring-relation hypothesis or faithful flatness.

Assume further `RingEtaleEquivalenceRelation t` and
`Module.FaithfullyFlat A B`. A flat-test groupoid cocycle specializes to the
three triple-coordinate points by the published `IsOneCocycle.specialize`
theorem; these points need no separate flatness hypothesis. The cocycle
equation and the comparison identity show that its image is killed by d1.
The degree-one Amitsur primitive theorem supplies m with d0(m) equal to
that image. The coboundary comparison and injectivity of
`amitsurCocycleEquiv` then give the original cocycle as the coboundary of m.
This proves `induced_oneCohomologyVanishes_of_faithfullyFlat`.

Finally, the source map is flat because it is étale. The published sufficient
criterion from `EtaleEquivalenceRelationCobar` therefore gives
`induced_isAcyclic_of_faithfullyFlat`, with exactly the unchanged invariant-lifting
predicate `IsAcyclic`. The coefficient universe v remains independent here;
the extension objects quantified by that predicate retain their published
universe.

The effective relation-ring presentation and faithful flatness are explicit
assumptions, not consequences proved in this module. This unit does not
construct a cover pushforward or prove the host task's geometric vanishing
statement. Its provenance is internal tensor algebra: it asserts no
identification with a separately constructed sheaf cohomology group.
