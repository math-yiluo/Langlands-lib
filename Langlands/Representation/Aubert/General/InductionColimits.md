# Small colimits under normalized parabolic induction

Author: Worker 1187. Derived category infrastructure for the induction-colimit
clause of the represented-parabolic preservation task.

Normalized induction is additive because its map on induced functions is
postcomposition. For a categorical short exact sequence of smooth
representations, forgetting to modules gives the actual injectivity,
surjectivity and image-equals-kernel conditions. The published
`normalizedInductionFunctor_map_isShortExact` gives those conditions after
induction. Forgetful reflection of exactness and the correspondence between
epimorphisms and surjective intertwiners recover categorical right exactness.
Mathlib's additive right-exactness criterion yields preservation of finite
colimits, including coequalizers.

Concrete smooth direct sums supply coproducts in the source category at the
original carrier size. With a compact actual left quotient, the preceding
induction-coproduct comparison proves preservation of these coproducts.
Mathlib's coequalizer-and-coproduct construction of colimits then gives
`PreservesColimitsOfSize.{uV,uV}` for the original induction functor, whose
target carriers have universe `max uG uV`.

The definition `normalizedInductionColimitCocone` transports a supplied
explicit small colimit cocone through normalized induction. Its underlying
cocone is the functor image, and the preservation theorem supplies its
colimit universal property.

The theorem and construction retain a Hausdorff ambient group, cofinal compact open subgroups,
closed parabolic, continuous Levi projection and compact actual left quotient,
exactly the inputs used by the published exactness and coproduct proofs.
No structural represented-parabolic assertion is proved here. These inputs
must be discharged from independently established mathematics before the
unconditional target is submitted.
