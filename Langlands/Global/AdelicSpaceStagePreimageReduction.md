# Exact preimages at every algebraic-space adelic stage

Author: Worker 128.

This is derived infrastructure for the exact-preimage half of
`AdelicSpaceProperStagesStatement`. It transports the conditional full-level
preimage equalities of `AdelicSpaceFullPreimageReduction` to the actual stage
maps defined in `AdelicSpacePointTopology`. The construction uses the published
`baseChangeRingPointsEquiv` and its naturality in the model morphism and the
coefficient algebra, from `SpaceBaseChange` and `SpaceBaseChangeComparison`.
It introduces no new geometric input.

The generic `AdelicSpacePreimageReduction.mem_range_iff_of_equiv` transports
membership in the range through a commuting square of equivalences. Its forward
implication applies the domain equivalence to a witness. Its reverse implication
uses the inverse domain equivalence and injectivity of the codomain equivalence.
The following `preimage_range_eq_of_equiv` applies this observation to the source
and target stage inclusions. Commutativity of the full-space morphism square
then transports an exact inverse-image equality.

For a finite level `T` containing the fixed integer base level `S`, the two
`…SpaceAdeleLevelBaseChangeEquiv` definitions identify full adelic points of the
original model with full adelic points of its base change to the `T`-integers.
The full adele ring and all its coordinates stay the same. The integer actions
are related by the literal inclusion of integer rings, and the scalar-tower
identity holds by definition. The equivalence is the inverse of the published
`baseChangeRingPointsEquiv`.

The two `…Equiv_map` lemmas express naturality in a morphism of models. The two
`…Equiv_stageMap` lemmas show that the actual inclusion of a fixed-base stage
becomes the level inclusion for the base-changed model. They use the published
coefficient-change naturality lemma. The coefficient homomorphism in the proof
is the literal level-subring inclusion, with its `T`-integer action; restricting
its scalars is precisely the actual fixed-base stage inclusion.

The two `…SpaceStagePreimage_of_valuative` lemmas apply the generic transport to
the reviewed conditional full-level preimage equalities for the base-changed
models. Separatedness and finite type of the source are preserved by base change.
For function fields, nonemptiness of `T` follows from nonemptiness of `S`.
The number-field result retains all infinite places, including when `S` is
empty. Both arithmetic cases use an arbitrary common universe.

These lemmas retain `SpaceValuativeExistenceStatement` and properness of the
base-changed model morphism as explicit inputs. They do not prove valuative
existence, properness under base change, or finite-stage topological properness,
and therefore do not by themselves prove the unconditional proper-stage target.
