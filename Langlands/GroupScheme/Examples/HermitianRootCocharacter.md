# The split diagonal cocharacter of the weighted Hermitian scheme

This internal construction builds an actual ground-field cocharacter of
`HermitianRoot.SchemeModel.groupScheme`. The data are a separable quadratic
extension of fields `L/k`, a finite middle index in `Type`, a conjugation-fixed
diagonal middle form `H`, and actual unit witnesses for its weights. The common
field universe is arbitrary, and no characteristic or anisotropy assumption is
used.

For every relative test scheme `T`, the existing
`SU3Root.SchemeModel.scalarUnit` includes a multiplicative test point into the
actual tensor coefficient algebra. These scalar units are fixed by quadratic
conjugation, by the existing `sectionToTensor_bar` lemma. Consequently the
actual matrix `diagonalEmbedding r`, whose entries are `r`, the identity middle
block and `r⁻¹`, belongs to the weighted determinant-one isometry subgroup.
Transport through the previously constructed full matrix point equivalence
defines `cocharacterPoints`. Its multiplicativity follows from the two actual
monoid homomorphisms for scalar units and diagonal matrices.

The coefficient lemma `map_diagonalEmbedding` is proved entry by entry. The
naturality of the matrix point equivalence and the existing scalar-unit
naturality then prove `cocharacterPoints_naturality`. The actual group-scheme
morphism `cocharacter` is obtained by `homOfPoints`. The final three lemmas give
its general-linear matrix, explicit diagonal matrix, and actual ambient tensor
matrix on every relative test scheme.

The provenance is internal: this extends the implemented SU3 cocharacter
construction to the previously constructed weighted Hermitian scheme using
the established weighted diagonal isometry lemma. It reuses the scalar and
tensor constructions by Lean name. It does not identify dynamic subgroups or
parabolic radicals, establish smoothness or reductivity, or prove general local
Kneser–Tits.
