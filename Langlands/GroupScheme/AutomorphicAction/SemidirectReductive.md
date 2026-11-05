# Reductivity of a semidirect product by a split torus

This internal, derived result proves that an actual semidirect product of a
pseudo-reductive group `G` by a split torus `S` is pseudo-reductive over every
field, in arbitrary characteristic and universe `u`. The proposition
`SemidirectSplitTorusPseudoReductivityStatement` quantifies over the actual group
schemes and their actual automorphic action. The theorem
`semidirectSplitTorusPseudoReductivity` proves this proposition.

The underlying scheme of the semidirect product is the relative product of the
two factors. Its affineness and smoothness follow from those of the factors.
A smooth connected affine group over a field is geometrically connected, so
this relative product is connected.

For triviality of the unipotent radical, let `U` be any smooth connected normal
closed unipotent subgroup of the semidirect product. Its projection to the split
torus is the trivial homomorphism. The published all-test factorization
`semidirectNormalSubgroup` therefore gives a homomorphism `i : U → G` whose
composite with the normal-factor inclusion is the original inclusion of `U`.
The factor is closed, and the published
`semidirectNormalFactor_isNormal` transfers its normality to `G`. The trivial
unipotent radical of `G` makes the range of `i` trivial on every scheme test.
Postcomposition by the normal-factor inclusion preserves that triviality,
proving the required assertion for `U`.

Over an algebraically closed field, a connected reductive `G` is
pseudo-reductive, and a pseudo-reductive group is connected reductive.
`isConnectedReductive_semidirectProduct_of_isAlgClosed` applies these two
published comparisons to the result above. It imposes no condition on the
automorphic action beyond the actual action axioms.

The provenance is internal: the proof combines existing semidirect-product
geometry, the vanishing of homomorphisms from unipotent groups to split tori,
all-test subgroup factorization and normality, geometric connectedness of field
group schemes, and the published comparison of the two reductivity predicates.
No external structural theorem or fixed-center-containing torus existence
assertion is assumed here. This unit supplies one ingredient for that existence
problem; it does not prove that problem unconditionally.
