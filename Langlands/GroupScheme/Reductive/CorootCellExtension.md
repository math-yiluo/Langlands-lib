# Extending the coroot cell map from a negative-simple translation law

This is an internal conditional construction using the published
`LocalSplitCell` generator-relation framework and `CellGluing.glueHom`.
It continues `CorootCellProjection` without asserting the full relative
derived-group existence theorem. Its essential remaining premise is the
explicit negative-simple translation relation, including nilpotent tests.

`positiveLawRelations_trivial` proves that every positive-factor relation
transfers to the target family consisting of zero homomorphisms from `𝔾ₐ`.
The target ordered products and the target root point are all the identity,
so the source relation is not needed for this conclusion.

`cellCompatible_corootCellProjection_of_negSimpleRelations` considers a
reductive group over any commutative ring, a fibrewise maximal coordinate
torus with a fibrewise root datum, a base of that datum, and supplied
simple-root parametrizations with Weyl-normalized points. A family of
simple words determines the root parametrizations of all roots by Weyl
conjugation. The root signs are enumerated for the cell formula.

The theorem assumes `NegSimpleRelations` for this source cell and the actual
coroot cell projection, with trivial target root maps. Concretely, on every
local ring with separably closed residue field, a relation obtained by right
translation by `u_{-a}(-1)`, for simple `a`, must preserve the coroot quotient
value. This hypothesis is not deduced from field points and does not assume
the base or test rings reduced.

The proof identifies the target Weyl family with the trivial family as an
equality of functions. The published positive-law theorem and the tautological
target laws give the simple positive-root relations. Torus equivariance gives
the torus relations. The supplied negative-simple relation and the published
Weyl-generation argument give all root relations. Finally
`cellCompatible_of_generatorRelations` gives compatibility on every relative
scheme test. Only the source cell is an open immersion; the quotient target
cell formula need not be one.

For any supplied open source cell and compatibility,
`corootCellExtension` is the actual group-scheme homomorphism constructed by
`CellGluing.glueHom`. Reductivity supplies smoothness and geometric
irreducibility of the source group required for that gluing theorem.
`cell_comp_corootCellExtension` proves its equality with the coroot projection
on the cell.

The source cell sends the torus section, with zero root coordinates, to the
given torus inclusion. Comparing both composites with that section proves
`inclusion_comp_corootCellExtension`: the extended homomorphism restricts
exactly to `corootProjection`. For finite root index,
`surjective_corootCellExtension` follows because its composite with the cell
map is the already surjective `corootCellProjection`.

This module does not prove the negative-simple relation, construct the
Weyl-normalized simple data, or establish smoothness or semisimplicity of
the extension's full kernel. Those remain additional obligations.
