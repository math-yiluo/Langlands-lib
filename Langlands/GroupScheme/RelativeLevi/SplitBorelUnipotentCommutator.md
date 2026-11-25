# Height commutator bounds inside the actual contracting group

This derived construction transports the supplied-cell height commutator
identity from the ambient group into an actual representative `j : U → G`
of its dynamic contracting subgroup. The base is an arbitrary commutative
ring in any universe, including the zero ring. The assumptions supply
torus-equivariant additive root maps, an open big-cell multiplication map,
strictly negative weights on the opposite factors, and strictly positive
weights on the chosen factors.

`liftedPositiveRootToUnipotent` reindexes the previously factored positive
root homomorphisms by `ULift (Fin n)`. This places their index type in the
universe required by the existing `rootFactor` interface. It changes
neither their order nor their values.

`exists_unipotent_commutator_eq_weight_ge` gives ordered positive-root
coordinates for the standard commutator `x y x⁻¹ y⁻¹` inside `U`, on
every scheme test. Coordinates whose weight is below the sum of the two
input weights vanish. Its proof applies the ambient supported-coordinate
identity to the reversed, negated inputs to convert its commutator
convention. Composing the proposed equality with `j` identifies each
factored root map with its ambient map and identifies the product with
ambient ordered multiplication. The representing morphism is monomorphic,
so cancellation proves the equality in `U`.

`commutator_unipotent_rootFactor_le` states the corresponding subgroup sum
bound for any supplied natural heights equal to the positive integer
cocharacter pairings. The root factors are the actual images of additive
global-function parametrizations in `U` on each test scheme. The proof
uses the preceding supported coordinates: every retained factor lies in
the height level at the sum of the input heights, and every lower
coordinate is zero.

The provenance is the explicit transport of
`LocalSplitHeightCommutator.exists_posComm_eq_weight_ge`, combined with
`SplitBorelPositiveFactors` and the definitions of `LocalSplitHeightSubgroup`
and `HeightFiltration`. Conrad, *Reductive group schemes* (2014),
Theorem 5.1.13, pp.143–145, motivates the actual contracting representative
and ordered positive product; Proposition 5.1.16, pp.146–148, motivates
the weight filtration. This module constructs the internal commutator
bound from the supplied data. Representing the height subgroups and their
successive vector quotients remains separate work.
