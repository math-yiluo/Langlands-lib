# Continuity under actual representation intertwiners

Author: Worker 585.

This helper module is internal derived linear algebra for the exact K0
realization proof. It uses the existing `FiniteRepresentation.IsContinuous`
predicate without changing it. For an arbitrary group `G` with an arbitrary
topology, continuity passes from the target to the source of an injective
intertwiner, and from the source to the target of a surjective intertwiner.
The two carrier universes are independent of each other and of the group
universe. The final lemma records continuity invariance under an actual
representation equivalence.

`isContinuous_subrepresentation` and `isContinuous_quotient` apply these
two general lemmas to the actual inclusion and quotient projection.
The constructors `continuousSubrepresentation` and `continuousQuotient`
bundle the resulting objects in the existing `ContinuousObjects G` type,
using the original subspace and quotient carriers in the original carrier
universe.

For an injection `i`, choose an ordinary complex linear left inverse `p`.
The source action at `g` is `p ∘ B(g) ∘ i`, by equivariance and the left
inverse identity. For a surjection `q`, choose an ordinary complex linear
right inverse `s`. Its target action is `q ∘ A(g) ∘ s`. The choices need
not intertwine the group actions.

In both cases the map from ambient endomorphisms to the recovered
endomorphism is complex linear. Mathlib's
`IsModuleTopology.continuous_of_linearMap` makes this map continuous for
the same module topologies on endomorphisms as in `IsContinuous`.
Composition with the given continuous action proves the result. No
continuity of group multiplication or inversion occurs in the proof,
and no invariant complement is required.

The module asserts no decomposition, semisimplicity or existence of
irreducible expansions. Its provenance is the displayed linear identities
and Mathlib's splitting and module-topology results, rather than a new
claim about the literature cited by the target statement.
