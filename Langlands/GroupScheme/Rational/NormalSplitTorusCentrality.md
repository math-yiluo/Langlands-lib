# Connected groups normalizing a split torus centralize it

Author: Worker 1549.

This internal consequence of the published torus-normalizer rigidity theorem
works over an arbitrary base scheme `S` in universe `u`. It adds no reductivity,
smoothness, finite-type, algebraic-closure or characteristic assumption.

The theorem `range_le_torusCentralizer_of_connected_of_isNormalizedBy` takes a
morphism `i : T.toGrp ⟶ G` from a split commutative torus whose underlying scheme
morphism is monic, and a group-scheme morphism `j : K ⟶ G` with connected
underlying scheme `K`. If the range of `j` normalizes the range of `i` on every
test scheme, it proves that the range of `j` lies in the all-test subgroup
functor `torusCentralizer i`.

The implemented proof applies
`TorusConjugation.exists_isNormalizingAut_of_connected` to the universal
`K`-point `j`. Normalization supplies both conjugation directions, using the
inverse point for the second direction. Rigidity supplies one automorphism of
`T` inducing conjugation on all points over all schemes mapping to `K`.
Evaluating this equation at the identity point of `K` shows that this
automorphism acts identically after composition with `i`. The same equation at
each arbitrary `K`-point then gives the required commutation on all tests.

The construction `connectedNormalizerCentralizerFactor` turns this containment
into an actual group-scheme morphism `K ⟶ C` whenever `c : C ⟶ G` represents
`torusCentralizer i`. It uses the published factorization through a represented
subgroup. The equation `connectedNormalizerCentralizerFactor_comp` proves that
composition with `c` is the original `j`. Representability is an explicit input
only to this data constructor; neither centrality theorem needs it.

The theorem `isCentral_of_isNormal_of_isSplitTorus` specializes to `K = G` and
`j = 𝟙 G`. Thus every normal monic split torus in a connected group scheme is
central in the published sense `IsCentral i`: every torus point maps into the
center on every test scheme, including after every refinement.

The provenance is internal: these results are deductions from the published
rigidity theorem and the existing definitions of normalization and centrality.
They provide the centrality step once a normal subgroup has been proved to be
a split torus. They do not establish that a smooth connected normal solvable
subgroup of a pseudo-reductive group is a torus, or prove the host task's
positive-root uniqueness statement.
