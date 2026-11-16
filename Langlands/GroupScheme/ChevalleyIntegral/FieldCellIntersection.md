# Flat field intersections with the ambient cell

This internal construction extends the parameter comparison of
`FieldCellFactor` from its schematically dense intrinsic cell to any scheme
mapping flatly to the field Chevalley group and compatibly to the ambient
matrix cell.

The general lemma `exists_factor_of_flat_cell_intersection` pulls back the
schematically dominant, quasi-compact intrinsic cell along the flat morphism.
The projection of this pullback remains schematically dominant. On the
pullback, the supplied parameter map and the ambient-cell map agree after
composition with the monomorphic ambient-cell inclusion, so they agree before
that inclusion. The published closed-immersion factorization lemma then
descends the parameter map to the original source.

`fullOrderedCellToAmbient` specializes the earlier closed parameter product
to all positive roots and all roots positive for the opposite data, together
with the full character-lattice torus. The distinctness and height ordering
of these published lists supply its closedness. Its composite with ambient
multiplication is the actual ordered matrix triple product.

The intrinsic field cell is affine and hence its multiplication to the affine
field group is quasi-compact. Its schematic density and parameter comparison
come from `FieldCellFactor`. The ambient-cell multiplication is an open
immersion and therefore a monomorphism. Applying the general lemma proves
`exists_orderedCellFactor` for a reduced root datum with finitely generated
character lattice. This does not assert that an integral closure has this
cell or has reductive fibres.
