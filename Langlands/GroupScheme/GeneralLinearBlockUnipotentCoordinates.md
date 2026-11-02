# Actual two-block unipotent coordinates

This is a derived comparison of existing constructions. For `a + b = n`,
`twoBlockWeight` assigns weight one to the first block and weight zero to the
second, using exactly the numbering of the original
`Langlands.GeneralLinear.blockUnipotent`. Either block may be empty.

`blockUnipotentCoordinates` extracts the upper right block. The two inverse
identities identify matrices `[[1, X], [0, 1]]` with the existing
`GroupScheme.GeneralLinear.blockUnipotentSubgroup` for these weights.
`blockUnipotentEquiv` expresses this as a group isomorphism from the additive
matrix group written multiplicatively. The original block multiplication
identity proves its homomorphism law. Entry evaluation supplies the continuous
inverse, and continuity of the original block matrix map supplies the forward
direction of `blockUnipotentHomeomorph`. Coefficient ring homomorphisms commute
with coordinate extraction.

For an arbitrary base ring and coefficient algebra, the existing subgroup
functor is evaluated on the actual affine test scheme. The global-sections
comparison identifies its membership condition with the same condition on the
actual coefficient matrix. `twoBlockPointsEquiv` and
`twoBlockPointsHomeomorph` therefore identify these actual subgroup points with
the original additive matrix coordinates, with the inherited point topology.
The topology comparison requires a topological coefficient ring and no
finite-type or smoothness hypotheses.

These constructions follow from the published block-matrix and actual-point
definitions by entry computations and the affine global-sections isomorphism.
They do not construct a represented unipotent group, a rational quotient,
compactness or a measure. Quotient and constant-term comparisons require
additional constructions.
