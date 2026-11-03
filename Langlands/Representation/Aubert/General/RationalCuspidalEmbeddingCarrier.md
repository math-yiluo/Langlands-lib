# Actual cuspidal embeddings with an independent input carrier

Author: Worker 1212.

This internal construction applies the published
`RationalPointFamily.rationalCuspidalEmbedding` to a universe lift and removes
that lift from the source of the actual embedding. The field universe `u`
and original smooth representation carrier universe `uV` are independent.
The original representation is retained as the source.

`cuspidalEmbeddingIndependentCarrier` takes exactly the structural and
topological inputs used by the published embedding theorem: a connected
reductive group over a nonarchimedean local field, a maximal split torus and
generic cocharacter, the standard-cocharacter, standard-Levi-intersection and
standard-endpoint statements, the actual relative root system, closedness of
the standard radicals and Levis, compactness of all standard parabolic left
quotients, and compact-subgroup containment for all standard radicals. The
rational-point topology is pinned to `pointTopology`; local compactness,
nonarchimedean structure and the Hausdorff property remain inputs.

For any irreducible `π` with carrier in `Type uV`, the result chooses an actual
standard index `I`, an irreducible smooth complex representation `σ` of that
standard Levi, and an injective intertwining map from `π` to the published
full-parabolic normalized induction of `σ`. The chosen `σ` satisfies the
published `IsLeviCuspidal` predicate for the same standard family. Its carrier
lies in `Type (max (u + 1) uV)`, as does its induced representation. The result
is a dependent pair containing these actual objects and the map, together
with the irreducibility, cuspidality and injectivity proofs.

The construction lifts `π` by `SmoothRep.universeLift` with lifting universe
`u + 1`. The existing representation equivalence proves that the lift is
irreducible. The published embedding theorem then gives the index, inducing
representation and injective morphism for this lift. Classical choice selects
these witnesses. Composing that morphism with the forward intertwiner of
`SmoothRep.universeLiftEquiv` gives the required map from the original `π`;
injectivity follows by composition.

This is derived carrier infrastructure. It proves no finite-length existence
result and no structural statement supplied as an input. It also does not
identify a source standard Levi or its cuspidality predicate with an ambient
dynamic Levi. Those comparisons, source reductivity, the structural proofs
and the supercuspidal finite-length theorem remain obligations of the exact
dynamic irreducible finite-length proof.
