# Detecting compact irreducible types with fixed vectors

This internal construction supports the compact-type argument in the concluding remark of Renard VI.3.4. Its provenance is the algebraic decomposition of a semisimple module into simple submodules, rather than a separate assertion from the source. It does not prove fixed-level finiteness or any rational-point twist comparison.

`exists_irreducible_projection_nonzero` writes the group-algebra module of a semisimple representation as a dependent direct sum of simple submodules. A nonzero vector has a nonzero coordinate. Coordinate evaluation is a complex-linear intertwiner onto the corresponding irreducible invariant subspace. The complex-linearity proof restricts scalars from the group algebra; equivariance evaluates the group-algebra action at a group element.

`CompactFixedType A K` records an irreducible compact-coefficient invariant subspace, a nonzero projection from `A`, and a nonzero `K`-fixed vector. `nonempty_compactFixedType` applies the preceding detection lemma to a nonzero fixed vector. A nonzero map to an irreducible representation is surjective, so compact smooth-dual coefficients pass to the detected type by the published surjective-image theorem. Equivariance preserves the chosen vector's fixedness. `detectCompactFixedType` chooses this data.

`compactRep` bundles the invariant subspace as an actual irreducible compact-coefficient smooth object. `inclusion` is its canonical embedding in the ambient representation. If two detected types are equivalent, `exists_nonzero_intertwiner` composes the source projection, the equivalence, and the target inclusion. Injectivity of the last two maps proves that this composite is nonzero.

The group and the two ambient carrier universes are independent. The construction requires semisimplicity and compact coefficients explicitly. It imposes no finite length, admissibility, finite dimension, or compact-open cofinality condition. The subgroup need not be open or compact.
