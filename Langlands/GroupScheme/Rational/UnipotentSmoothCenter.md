# Smooth stable central subgroups from uniform nilpotence

This derived development constructs a nontrivial smooth stable central closed
subgroup of a nontrivial smooth connected affine group over any field, assuming
a uniform nilpotence bound on all its groups of scheme-valued points. It then
discharges that bound for an unipotent ambient group. All declarations retain
an arbitrary universe `u`.

Its provenance is the explicit argument below using
`Rational.UnipotentPointsNilpotent`, `ImageGenerationPointed`,
`ImageEnvelopeStabilityProof`, `SmoothConnectedGeometryProof`, and
`NormalizerRepresentability`. It imports these results by Lean name and does
not assume central-vector-subgroup existence.

`IteratedCommutator.source G n` is the nested product of `n+1` copies of the
underlying group scheme. Its morphism `word G n` is the identity for `n=0`,
and the commutator of the preceding word and one further group point at the
next index, with convention `[x,y] = xyx⁻¹y⁻¹`. Every value belongs to abstract
lower central term `n`. Applying the uniform all-test nilpotence bound to the
universal point of the word's own source makes that word the constant unit
morphism. The origin of every nested source is the tuple of units, and its
image is the unit.

The first such constant unit word has positive index if the ambient group functor
is nontrivial. Its preceding word is nontrivial and its whole image lies
in the all-refinement centre. Over a field the centre has a closed subgroup
representative by the existing centralizer representability theorem applied
to the identity inclusion. Minimality of the closed image envelope thus puts
that envelope inside the centre. This avoids assuming that its arbitrary
test points are global products of source points.

The nested source carries the recursively constructed diagonal action, and
the word is equivariant on every test scheme because the ambient action
preserves multiplication and inverses. For a smooth connected affine group,
the published geometric integrality theorem and its product preservation
show that the source is affine, locally of finite type and geometrically
integral. Pointed image generation then supplies an actual smooth affine
geometrically connected closed subgroup representing the fixed closed
envelope. Over a field geometric connectedness gives connectedness.

`HasNontrivialSmoothStableCentralSubgroup b` records an actual smooth,
affine, geometrically connected and connected nontrivial central closed
subgroup, an actual restricted action, stability and the all-test
equivariant inclusion. Here nontriviality means that the inclusion's subgroup
functor is not the bottom functor; the ambient nontriviality hypothesis has
the same form for its identity homomorphism.

`hasNontrivialSmoothStableCentralSubgroup_of_uniformNilpotence` proves this
predicate for any affine acting group `H` and any actual automorphic action
on the smooth connected affine group `G`, given ambient nontriviality and
`∃ d, HasUniformNilpotentPoints G d`. Envelope stability for the equivariant
word gives the restricted actual action. Centrality follows from the closed
centre and envelope minimality. If the envelope were trivial, the actual
factorization of the word through its representative would make the word
constant at the unit, contradicting its choice.

`hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent` uses the proved
uniform nilpotence bound for affine locally finite type unipotent group
schemes. Smoothness supplies local finite type. Both theorems hold over an
arbitrary field; algebraic closedness, perfectness and a torus assumption on
the acting group are unnecessary.

The predicate and conclusions do not assert unipotence of the subgroup,
vector coordinates, positive relative dimension or linearity of the
restricted action. They do not prove `CentralStableVectorSubgroupStatement`
or the host `SemigroupOrderedProductStatement`; those remain separate
obligations.
