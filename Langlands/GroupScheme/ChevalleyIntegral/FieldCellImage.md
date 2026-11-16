# Ordered integral cells in the field Chevalley subgroups

This internal construction fixes a Dedekind base, its fraction field, a supplied
generic Chevalley group, an arbitrary field-valued base point, and any supplied
field Chevalley group for the same datum. The two root lists are arbitrary.

The existing `root_fieldEmbedding` and `torus_fieldEmbedding` identities say that
the supplied field roots and full torus equal the integral generators after
base change, with the canonical additive and diagonalizable source comparisons.
The pullback adjunction is a multiplicative equivalence on points on every test
scheme. Consequently each integral generator point on a field test scheme
factors through the field Chevalley embedding. The subgroup of points in this
embedding image is closed under products. Induction on the root lists and the
three-factor product therefore gives
`orderedCellProduct_comp_mem_fieldEmbedding`.

Apply this all-test result to the base-changed parameter scheme and its
canonical projection to the integral parameter scheme.
`fieldOrderedCellFactor` chooses the resulting actual morphism into the field
Chevalley group; `fieldOrderedCellFactor_comp` identifies its composite with the
closed field embedding with the base change of the integral ordered product.
This is a scheme-morphism factorization, not only an assertion on field-valued
points. Neither reducedness nor positivity assumptions on the lists are needed.

This module supplies the image-containment part of the full-field open-image
condition. It does not assert that the ordered product is open or that its source
is nonempty. Its provenance is internal: it combines `IntegralCellProduct`,
`FieldEmbedding`, and the published multiplicative pullback point equivalence.
