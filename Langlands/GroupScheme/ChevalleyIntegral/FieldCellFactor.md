# Field Chevalley cells and ordered root parameters

This internal construction compares the published intrinsic dynamic triple cell
of a field Chevalley group with its ordered negative-root, full-lattice torus,
and positive-root parameter product.

The field coefficient recovery defines a morphism from the ambient matrix group
to the positive root parameter space. Its composite with the ordered-root map
is the published field retraction endomorphism. The identity of this
endomorphism on the dynamic positive unipotent subgroup supplies the factor
`unipotentToOrderedRoots`. Applying the same construction to the opposite
Chevalley data supplies the negative factor. The opposite regular cocharacter
is the original regular cocharacter precomposed with inversion, as follows
by composing with the closed matrix inclusion and comparing diagonal weights.

The dynamic centralizer maps to the full-lattice torus using the published
all-test-scheme centralizer containment. The three factors together define
`intrinsicCellToOrdered`. Its ordered matrix product is exactly the intrinsic
dynamic triple-cell multiplication followed by the matrix inclusion.
The intrinsic multiplication is schematically dense by the published
triple-cell theorem for smooth connected affine field groups.

Reducedness of the root datum is required for the unipotent retraction
identity. Finite generation of the character lattice is required for the
centralizer containment. The construction does not assert an integral cell
identification or reductivity of an integral model.
