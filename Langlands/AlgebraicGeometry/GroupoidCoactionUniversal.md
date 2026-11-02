# Universal points and coaction identities

Author: Worker 101.

This is an internal algebraic construction derived from the published
`RingEtaleEquivalenceRelation` and `GroupoidCoaction`, which remain unchanged.
It supplies the universal points needed for constructing kernel coactions;
it does not claim the Serre criterion.

The generation hypothesis says that the source image together with the
target image generates the relation ring. Thus two maps out of that ring
agree if their restrictions to the source and target agree. The proof
expresses their equality locus as a subalgebra and applies the generation
hypothesis. Reflexivity at the identity of the base ring supplies an
identity point `identity : C →ₐ[B] B`.

The categorical ring pushout of the source and target maps represents two
composable points. Its maps `composableFirst` and `composableSecond` satisfy
the published composability equation, and transitivity supplies their
`composableComposite`. The source algebra on this pushout is flat: its
second structural map is the base change of the flat source map, and the
source map followed by it is again flat. The source map is flat because it
is étale. No flatness of an arbitrary test ring is asserted or used.

Every diagonal point factors through `identity`. Every composable pair
factors through the pushout, and its composite agrees with the specialization
of `composableComposite`, by the uniqueness just proved. The tensor maps
are natural under these specializations; their scalar and composite
identities are proved by tensor induction. Consequently `ofUniversal`
constructs a coaction from a semilinear additive map whose unit and cocycle
identities hold at the two universal points. Its underlying coaction is the
supplied additive map. This turns those two universal identities into the
full pointwise identities of the published definition, for every test ring
in the prescribed universe.

All rings are in an arbitrary universe `u`, and the module may be in an
independent universe `v`. The construction uses classical choices of the
identity and composite points from the existing existential axioms of the
relation. It introduces no mathematical axioms or descent assumptions.
