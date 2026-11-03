# The proper-centralizer step of Borel normalizer induction

This internal helper implements the proper-subgroup step needed for the
pointwise Borel normalizer theorem. It retains the geometric intersection
hypothesis and the smaller-group induction hypothesis explicitly. It does not
prove `BorelNormalizerStatement`.

`BorelNormalizerProperty G` is the exact conclusion of the published
`BorelNormalizerStatement` for one group over its ground field: for every
`IsBorelSubgroup i`, the abstract normalizer of the image of its ground-field
points is that image. The predicate itself requires only a field; smoothness,
affineness, connectedness and algebraic closedness occur in the published
global target. `borelNormalizerStatement_iff` identifies that target
definitionally with the assertion of this local property for all groups
satisfying its original hypotheses.

`borelNormalizer_lieDimension_induction` specializes the published strong
induction principle to this local property. Its induction hypothesis ranges
over all smooth connected affine groups of strictly smaller
`Lie.dimension`, including groups without a specified embedding into the
current group. No dimension decrease for a quotient is asserted.

For a monic `j : M ⟶ G`, suppose `c : C ⟶ M` is Borel and
`range (c ≫ j) = range j ⊓ range b` on all test schemes. Suppose also that
`BorelNormalizerProperty M` holds. Then
`mem_borelRange_of_normalizes_intersection` proves that any ground-field
point of `G` normalizing the point subgroup of `b` and lying in the range of
`j` lies in the range of `b`. The proof lifts the point through `j`, applies
the point-normalizer preimage theorem to show that this lift normalizes
`range c`, and uses the local normalizer property of `M`. The resulting
lift through `c` maps into the prescribed intersection, hence into `range b`.
The theorem does not require that `b` itself be Borel.

`mem_borelRange_of_proper_intersection` obtains the local property of `M`
from the smaller-group induction hypothesis when `G` is smooth connected
affine, `M` is smooth connected, and `j` is a closed subgroup inclusion
which is not an isomorphism. Closedness supplies the affineness of `M` and
the monomorphism. The published strict Lie-dimension theorem supplies the
inequality needed by induction.

`mem_borelRange_of_proper_subgroupIntersection` applies this result to the
canonical scheme-theoretic pullback intersection using its all-test range
identity. It retains the premise that the first intersection projection is
Borel in `M`.

`mem_borelRange_of_proper_cocharacterCentralizer` specializes further to a
closed representative of `Dynamic.centralizer χ`. It obtains smoothness of
`M` from the proved `dynamicSmooth` theorem and converts the point's
centralizer membership to range membership through the representation
equality. Connectedness of `M`, properness of the inclusion, the Borel
intersection premise and the smaller-group induction hypothesis remain
explicit. No normalizer representability or smoothness premise is used.

All constructions are universe-polymorphic. The provenance is internal:
these are compositions of the published Borel target, actual Lie-kernel
dimension induction, subgroup intersection, and dynamic smoothness APIs,
with the normalizer preimage helper. The central quotient case, torus
commutator dichotomy, and geometric proof that the intersection is Borel
remain outside this helper.
