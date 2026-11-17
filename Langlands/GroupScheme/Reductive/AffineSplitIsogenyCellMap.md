# Powered big-cell maps and their conditional extensions

This internal construction combines the actual torus and root maps of
`AffineSplitIsogenyTorusMap` and `AffineSplitIsogenyRootMap` with the published
one-way gluing theorem `CellGluing.glueHom`. It is a supporting step toward the
affine split isogeny theorem. Compatibility of different root groups remains
an explicit premise; this module does not prove that premise or the final
isogeny theorem.

For a root-datum isogeny `f : RootDatumIsogeny p Q P`, the family
`poweredRootFamily` is indexed by the source roots. Its member at `j` is the
target root parametrization at `f.indexEquiv.symm j`, precomposed with the
additive power having exponent `f.rootFactor (f.indexEquiv.symm j)`. The
characteristic condition is exactly the condition used in the published
affine target. On every relative scheme test its value at `c` is the target
root point at that power of `c`.

`poweredRootFamily_equivariant` reindexes the proved root-character
equivariance. Thus the powered target family transforms through the source
root characters under `torusMap f` followed by the target torus inclusion.
`poweredCellMap` is the resulting actual morphism from the source coordinate
cell: the ordered negative powered factors, the prescribed image of the
torus coordinate, and the ordered positive powered factors.

For any source family of actual root parametrizations whose cell map is
monic, torus translation relations transfer to this powered target cell.
The proof applies `torusRelations_of_equivariant` to the two families with
their common source characters. If the source cell is an open immersion and
the source group is reductive, `cellCompatible_poweredCellMap_of_rootRelations`
reduces compatibility on every scheme test to the explicit `RootRelations`
premise over local rings with separably closed residue field. It uses the
published one-way `cellCompatible_of_generatorRelations`. This assertion
requires an affine target, but does not require an open target cell.

For any compatible powered cell with an open source cell,
`poweredCellExtension` is an actual group-scheme homomorphism. Reductivity
supplies the smoothness and geometric irreducibility needed by `glueHom`.
The cell-composition theorem identifies its restriction to the whole source
cell with the powered formula. Precomposing with the published torus section
gives exactly `i ≫ poweredCellExtension = torusMap f ≫ i'`.

The two single-coordinate cell lemmas identify cell points with one nonzero
negative or positive coordinate as the corresponding root points. They use
the existing ordered-product lemma, which sets every other factor to the
identity. Precomposing the cell-composition theorem with those points proves
the prescribed power formula for every root appearing in either ordering,
on every relative scheme test. Finally `CellGluing.hom_ext_cell` proves that
agreement with the powered cell determines the ambient homomorphism uniquely.

The construction works over any commutative ring, including the zero ring.
The powered target maps are not assumed to be monic or open immersions.
No root-relation normalization, exceptional rank-two polynomial identity,
fibrewise isogeny criterion, or unconditional ambient existence claim is
included here.
