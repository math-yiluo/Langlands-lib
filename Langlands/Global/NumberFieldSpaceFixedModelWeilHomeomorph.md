# Full adelic homeomorphism for an original number-field space Weil model

This internal unit constructs the full adelic homeomorphism for a fixed original
integral model and its Weil restriction. It retains representability and the
separated finite-type geometry of the original Weil model as explicit inputs.
It does not compare arbitrary models or identify the generic-fibre Weil map.

Let `L/K` be an extension of number fields and let `S` be a finite set of finite
places of `K`. Let `X` be an algebraic space over the upper integers outside the
full preimage of `S`. Assume `X` is separated and of finite type, that its
original Weil sheaf to the lower S-integers is algebraic, and that the resulting
space `W` is separated and of finite type. Both full point spaces carry their
previously defined final topologies from all arithmetic stages.

`stageMap_transition` proves that enlarging a stage before including its points
into the full adeles gives the original stage map. This follows from composition
of coefficient change and the literal inclusions.

`adelicEvaluation_injective` proves injectivity of the original full counit
evaluation. The published filtered-ring point comparison supplies a stage for
each source point. After enlarging to a common lower stage, the full evaluation
stage identity expresses both images through the same upper stage. Separatedness
of `X` makes the coefficient change from that stage to the full adeles injective,
since the original ring inclusion is injective. The original stage homeomorphism
is injective, so the two source stage points and their full images agree.

`adelicEvaluation_surjective` starts from an upper stage containing the target
point. The published `numberFieldLevelCover` produces a lower support whose
full upper preimage contains that stage. Enlarge the upper stage, apply the
inverse original stage homeomorphism, and include this lower point into full
adeles. The full evaluation stage identity and `stageMap_transition` show its
image is the specified point. `adelicPointEquiv` uses these proofs to make the
original counit evaluation an equivalence.

`forward_stage_lifts` uses the original stage homeomorphisms, their continuity,
and the evaluation stage identity. `backward_stage_lifts` sends each upper stage
to its cofinal enlargement followed by the inverse original stage homeomorphism.
The published transition theorem gives continuity of the enlargement, so this
lift is continuous. Injectivity of `adelicPointEquiv`, its inverse identity, and
the full evaluation stage identity verify its commutative square.

`adelicPointHomeomorph` applies `homeomorphOfStageLifts` to these continuous lifts
in both directions. The source and target are exactly the previously defined
full adelic point types and their final stage topologies. Its forward function
is the original full counit evaluation, as recorded by
`adelicPointHomeomorph_apply` by definitional equality.

The provenance is internal composition of published point coverage, injectivity
for separated spaces under injective coefficient change, arithmetic support
cofinality and transition continuity, the actual stage homeomorphisms and their
original counit identities, and the general final-topology comparison theorem.
All infinite places remain in the original stage comparisons.

Stage transitions reuse
`AdelicSpacePointsProof.numberField_stageMap_transition` with the original
space and literal coefficient maps.
