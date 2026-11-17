# Positive layers with possibly zero weights

Author: Worker 204.

This internal extension of `HeightFiltration` and `HeightLayer` permits
arbitrary natural weights on the finite ordered family of actual
subgroups. It retains the sum bound on commutators and requires the
cutoff `d` to be positive. Zero-weight factors can therefore remain in
the full coordinate family, although they are discarded from every
positive level.

`commutator_factor_le_of_pos` proves the strict increase needed for
ordered collection. If either input weight is below the cutoff, that
factor is trivial. Otherwise both input weights are at least the
positive cutoff, so their sum strictly exceeds their maximum. The sum
bound then expresses their commutator using retained factors of strictly
larger weight. The existing `HeightCollection` theorem gives
`exists_coords_of_pos`: every element of a positive level has an ordered
factorization with each coordinate below the cutoff equal to the
identity. No reordering or removal of indices is required.

`layerMap_surjective_of_pos` applies those coordinates to an element of
the level. Coordinates above `d` disappear in the quotient by level
`d+1`, and those below `d` are already trivial. The exact-weight
coordinates thus represent the original quotient class.

For `layerMap_injective_of_pos`, assume also that the full ordered
product on the original subgroup family is injective. The product of a
tuple in the layer map's kernel lies in level `d+1`. Collection at that
positive cutoff supplies another factorization whose coordinates below
`d+1` are all trivial. Uniqueness of the full coordinates forces the
original exact-weight tuple to be trivial. `layerEquivOfPos` packages
the resulting multiplicative equivalence between the product of the
exact-weight subgroups and the actual successive group quotient.

All definitions of levels, layers, projections and the layer map are
the existing ones. The provenance is internal group theory: these
proofs extend the earlier positive-weight arguments by using positivity
of the retained cutoff in place of positivity of the entire weight
family. They impose no order condition on the weights. Scheme
representability and the identification of these weights for a
parabolic radical remain separate obligations.
