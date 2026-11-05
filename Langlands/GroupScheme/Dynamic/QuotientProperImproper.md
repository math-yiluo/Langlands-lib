# Supplied quotients by full dynamic subgroups

Author: Worker 1228.

This internal construction identifies the actual supplied quotient by a full
dynamic subgroup with the base scheme. It supplies the improper cases of the
separate `DynamicQuotientProperStatement` problem. It does not prove properness
when the dynamic subgroup is smaller than the full group.

The construction works over any base scheme `S`, for any group scheme `G`,
relative scheme `Q` and morphism `q : G.X → Q`. If the underlying morphism of
`q` is an epimorphism and every two points on every relative test scheme have
the same image under `q`, `fullQuotientIso` constructs
`Q ≅ Over.mk (𝟙 S)`. Its forward map is the structure morphism of `Q`.
Its inverse is the composite of the group identity section with `q`.

To verify the first inverse identity, the implemented proof applies the
all-test hypothesis to two points on the test scheme `G.X`: the identity map,
and the constant point given by the identity section. Cancellation of the
epimorphism `q` then proves that the structure morphism followed by the
displayed section is the identity of `Q`. The other inverse identity is the
condition that the section is a morphism over `S`.

For `suppliedQuotientIsoOfParabolicEqTop`, smoothness, surjectivity and
quasi-compactness make `q.left` an effective epimorphism using Mathlib's fpqc
result, hence an epimorphism. If `Dynamic.parabolic χ = ⊤`, the given exact
right-coset fiber criterion says that every pair of points has the same image.
The generic construction therefore identifies this same `Q` with the base.
Its structure morphism is an isomorphism and is proper. The final two lemmas
specialize this to the trivial cocharacter and to a cocharacter whose dynamic
centralizer is full, using the published `Dynamic.ImproperParabolic` results.
No field, characteristic, reductivity, or separatedness hypothesis is needed.
The test schemes remain arbitrary schemes over `S`.

This is a derived categorical construction, not a transcription of a result
from Milne. The source's full-subgroup quotient is the base; here that
description is proved directly for the supplied quotient using its fiber
criterion. No assertion of parabolicity or properness in the general reductive
case enters this proof. In particular, none of the regular-cocharacter/Borel,
rank-one obstruction or positive-root uniqueness results is imported or used.
