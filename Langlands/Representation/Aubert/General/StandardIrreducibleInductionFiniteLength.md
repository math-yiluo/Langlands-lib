# Finite-length ambient embedding for standard irreducible induction

Author: Worker 1212.

This internal construction applies to an actual standard Levi over an arbitrary
nonarchimedean local field. The original representation carrier universe is
independent of the field universe. It retains the exact universal cuspidal
induction finite-length statement at the enlarged coefficient universe, the
standard-cocharacter and standard-Levi-intersection statements, the relative
root-system property, closedness of the standard radicals and Levis, and
compactness of the displayed inside-Levi parabolic quotients.

`StandardIrreducibleInductionEmbedding` stores a smooth coefficient
representation of the original standard Levi, the actual intertwining map
from normalized induction of the original representation to normalized
induction of that coefficient, its injectivity, and finite length of the
target. The coefficient and target have carrier universe `max (u + 1) uV`.
The source has its original induced carrier universe `max u uV`.

`standardIrreducibleInductionEmbedding` chooses these data under the retained
inputs above. The construction lifts the original irreducible representation's carrier
to `max (u + 1) uV`, uses `exists_cuspidal_embedding_in_levi` to embed it into
actual normalized induction from irreducible cuspidal data, and applies the
supplied cuspidal-induction finite-length statement. The published actual
standard induction-in-stages isomorphism identifies the induced embedding's
target with that finite-length representation. The original embedding is the
composition with the universe-lift equivalence. `normalizedInductionMap`
postcomposes induced functions with that coefficient embedding, and
`normalizedInductionMap_injective` supplies its injectivity across the independent
carrier universes. The target finite-length evidence is transported through the
actual stages isomorphism. An existential witness is first constructed in
`Nonempty`, then selected by `Classical.choice`; no canonical choice is asserted.

The corollary `standardIrreducibleInduction_hasFiniteLength` uses the stored
injective intertwiner as a group-algebra linear map. Finite length of its target
descends to the original normalized induction by `IsFiniteLength.of_injective`.

This composes published constructions and proves no retained structural or
cuspidal-induction finite-length input. It is an intermediate reduction for
VI.6.2, not a proof of the unconditional dynamic target.

The groups in this result are the literal standard rational-point subgroups
`parabolic i ν K`, `levi i ν K` and `unipotent i ν K` of `G(k)`, with the
canonical point topology. The normalized functor is the published
`normalizedInductionFunctor`, including its half Haar-modulus character on
the full parabolic. The standard stages isomorphism uses that same
normalization. The input representation has carrier universe `uV`; its induced
representation has carrier universe `max u uV`. The lifted coefficient and the
finite-length target used during the proof have carrier universe
`max (u + 1) uV`.

The provenance is internal: this result composes the published
`exists_cuspidal_embedding_in_levi`,
`standardInductionStagesIso_of_standardData`,
`isIrreducible_universeLift_iff`, and
`normalizedInductionMap`, `normalizedInductionMap_injective`, and
`IsFiniteLength.of_injective`. The cuspidality in the
intermediate embedding is precisely `IsLeviCuspidal` for the ambient standard
family, as required by the retained
`RationalSupercuspidalInductionFiniteLengthStatement`; no comparison with a
different intrinsic cuspidality condition is asserted.
