# Actual weight-vector coordinates on root subgroups

This internal derived unit retains the torus equivariance of the vector
coordinates already supplied by the published cyclic weight quotient.
The ambient group scheme is smooth and affine over an arbitrary field, and the
acting torus is split. For a nonzero character `a`, `HasNoHigherRoots i a`
excludes every multiple `n • a` with `n ≥ 2` from the actual relative roots.
For every supplied representative `j : U ⟶ G` of the actual root subgroup
functor, the module constructs natural vector coordinates in which the full
torus action `subgroupAction i a j hj` is multiplication by `a`.
The coordinate equivalences and action formula hold on every scheme over the
ground field, including nonreduced tests.

`IsWeightVectorCoordinates.of_equivariantIso` first transports a supplied
coordinate system along an actual equivariant group-scheme isomorphism.
Postcomposition with its forward map is an isomorphism on every group of
points. Associativity proves naturality of the transported coordinates, and
the equivariance equation proves their weight formula.

`exists_weightVectorCoordinates_of_noHigherRoots` identifies the first cyclic
filtration term with the actual root functor using
`cyclicRootFunctorComparison`. The published higher-root vanishing theorem
identifies its second term with the trivial subgroup functor. Applying
`cyclicWeightFiltration` to the supplied representative gives a vector quotient
with a compatible torus action and the two equivariance equations for its
inclusion and quotient map. The inclusion is monic, so the inverse image of
the trivial subgroup is trivial. Thus this quotient has trivial actual kernel,
and `IsFppfQuotient.isoOfBot` makes the quotient map an actual group-scheme
isomorphism. Cancelling the monic inclusion identifies the filtration's source
action with `subgroupAction`. The transport lemma then pulls the quotient's
weight coordinates back to `U`.

`weightVectorCoordinatesOfNoHigherRoots` chooses and returns this coordinate
data as a dependent pair: its finite dimension, its equivalence on every test
scheme, and the naturality and weight-equivariance proof. This construction
lets consumers work with a coordinate system directly, without making their
own choices from the existence theorem. The choice does not prescribe a basis.

`hasUniqueWeightVectorStructure_of_noHigherRoots` combines these coordinates
with the published uniqueness of scalar multiplication in weight coordinates
for a nonzero character of a split torus. It asserts independence of scalar
multiplication from the choice of coordinates, rather than uniqueness of a
basis.

The provenance is an internal composition of the imported Library proofs.
Worker 1368 identified the need to retain the quotient's equivariance for the
pinned-rigidity argument and suggested the trivial-kernel transport route.
The existing `isVectorGroup_of_noHigherRoots` forgets this equivariance; the new
result preserves it. No connectedness, reductivity, maximality, characteristic
or perfectness assumption is added. The character need not itself be an
actual root, and the finite dimension is not asserted to be positive or one.
No opposite-factor-pair existence, root fixedness or pinned rigidity theorem
is proved here.
