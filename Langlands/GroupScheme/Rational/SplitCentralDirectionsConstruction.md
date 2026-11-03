# Actual split-component realizations of all central directions

Author: Worker 1319.

This is an internal assembly of the actual group-scheme, lattice and real-space
constructions already used by `RelativeSplitCentralDirectionsStatement`.
It has two explicit unproved inputs: `RootAnnihilatorCentralityStatement` and
`CharacterRestrictionStatement`. It does not assert an unconditional proof of
either input or of the full target.

For a smooth connected affine group over any field, a split torus mapping
monomorphically into it, and a split component factored through that torus,
`IsSplitComponent.range_cocharacterMapReal_eq_relativeCentralDirections`
identifies the actual real cocharacter image with the common annihilator of
all actual relative roots. In the forward direction, each actual root restricts
to zero on the central split torus. In the reverse direction, the first input
makes every integral root-annihilating cocharacter central. The integral
split-component factorization and finite-root base-change lemmas then give
containment of the entire real annihilator in the image. Neither independence
of roots nor a reduced root-system hypothesis is used.

`IsSplitComponent.cocharacterEquivCentralDirections` is the actual real
cocharacter map, viewed as a linear equivalence onto this annihilator when
its underlying morphism is monic. Its coercion theorem records that it maps
each vector by `cocharacterMapReal f`.

`IsSplitComponent.restriction_kernels_eq_relativeRootSpans` identifies the real
restriction kernel by the perfect actual character–cocharacter pairing and
double annihilation. Faithful rational-to-real scalar extension descends this
identity to the full rational character space.

Finally, `relativeSplitCentralDirections_of_centrality_characterRestriction`
has exactly the full arbitrary-universe Library target as its conclusion.
The published split-component existence theorem supplies a component for the
dimension and fixedness clauses. Its actual embedding identifies its real
cocharacter space with the central directions, and the second input identifies
its rank with the rational-character rank of the ambient group. Centrality
makes the actual quotient relative Weyl action fix this image pointwise.
The same image and kernel arguments apply to every supplied split component.
The full character and cocharacter dimensions use the published finite split
torus coordinate constructions. Empty root sets and rank zero are retained.

All arguments are derived from the imported declarations. There is no external
source claim and no additional realization, rank, complement or faithfulness
premise.
