# Stable coordinate lines of unipotent group schemes

This internal construction uses the published actual representation on split
invariant coordinates and the definition of `IsUnipotent`. It uses no external
structural theorem.

Over a commutative ring, for a finite coordinate index set and a chosen index `j`, the inclusion of the
line spanned by the coordinate unit vector and the projection onto its `j`th
coordinate are rectangular matrices with composite equal to the identity.
If every test point of an actual representation carries this unit vector to a
scalar multiple of itself, these matrices satisfy `IsStableCoordinates`.
`coordinateLineRepresentation` is the resulting actual one-dimensional
group-scheme representation. Scalars are allowed to depend on the test point
and are not assumed to be units.

For a unipotent group over an arbitrary field, this representation has a nonzero
fixed vector by the existing definition of unipotence. Its sole coordinate is
nonzero. The coordinate inclusion transports it to a fixed vector in the
original representation; multiplication by the inverse of its coordinate
recovers the coordinate unit vector. Thus `isFixedVector_single_of_isUnipotent`
proves that the stable coordinate line is fixed pointwise on every relative
scheme test. No affineness, smoothness, perfectness, or rational-point
surjectivity is assumed.

This is a prerequisite for constructing a representation whose kernel is a
given unipotent normal subgroup. It does not construct that representation or
prove affineness of a quotient.
