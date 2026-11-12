# Full adelic homeomorphism for an original curve-place space Weil model

This internal unit constructs the full adelic homeomorphism for a fixed original
principal integral model and its Weil restriction. Representability and the
separated finite-type geometry of the original Weil model remain explicit inputs.
This unit does not compare arbitrary models or identify the generic-fibre Weil map.

Let `k` be finite, let `K` be a function field over `k`, and let `L/K` be finite.
Fix `s`, a finite-dimensional extension of `k(s)` to `K`, and a nonzero chart
element `t`; these specify the original principal integral base and exceptional
support `S`. Retain a function-field structure on `L` and assume `S` is nonempty.
Let `X` be an algebraic space over the upper integers outside the full preimage
of `S`. Assume `X` is separated and of finite type, its actual Weil sheaf over
the lower integral base is algebraic, and the resulting Weil space `W` is
separated and of finite type. No separability hypothesis on `L/K` is used.

Both full point spaces have their previously defined final arithmetic stage
topologies. The published `AdelicSpacePointsProof.curve_stageMap_transition` records that enlarging a stage before including
it into full adeles gives the same literal map. Its proof is the composition law
for coefficient change and the equality of the original inclusions.

`adelicEvaluation_injective` places each of two source points in arithmetic
stages using the published filtered-ring point comparison. Enlarge to a common
lower stage. The full evaluation stage identity puts both images in the same
upper stage; separatedness of `X` and injectivity of the original stage ring
inclusion make its point map injective. Injectivity of the original stage
homeomorphism therefore gives equality of the lower points and their full images.

`adelicEvaluation_surjective` starts from an upper stage containing a given target
point. The published `curveLevelCover` provides a lower support whose full upper
preimage contains that stage. Enlarge the upper stage, apply the inverse original
stage homeomorphism, and include the result in the lower full point set. The
stage evaluation identity and `AdelicSpacePointsProof.curve_stageMap_transition` show that this point maps to
the specified target. `adelicPointEquiv` packages this bijective original counit.

`forward_stage_lifts` uses the continuous original stage homeomorphisms and the
full evaluation stage square. `backward_stage_lifts` uses the transition to the
cofinal full-preimage stage followed by its inverse homeomorphism. The published
curve stage transition theorem proves continuity; its upper support nonemptiness
is supplied by the original regrouping lemma. Applying the counit equivalence,
using its inverse identity and the stage square verifies the backward lift.

`adelicPointHomeomorph` applies `homeomorphOfStageLifts` to the equivalence and these
continuous lifts in both directions, with exactly the original full adelic point
types and final topologies. `adelicPointHomeomorph_apply` identifies its forward
function with the original full counit evaluation by definitional equality.

The provenance is internal composition of published point coverage, separated
coefficient injectivity, directed supports, actual upper-place cofinality and
stage transition continuity, the original space Weil stage homeomorphisms and
their counit evaluation squares, and the general final-topology comparison.
