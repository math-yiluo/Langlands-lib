# Actual two-block unipotent rational quotient

This derived construction compares the actual rational quotient of the existing
two-block subgroup functor of the general linear group scheme with the original
matrix space over `AdeleQuotient`. Both block sizes may be zero. The weight and
numbering are the ones in `GeneralLinearBlockUnipotentCoordinates`.

`rationalCoordinates` and `adelicCoordinates` specialize the actual affine-point
coordinate comparisons. `adelicCoordinates_rational` proves that the restricted
principal map is entrywise diagonal coefficient extension, using naturality of
the existing general-linear point comparison.

`quotientCoordinates` reduces the actual adelic matrix coordinates modulo the
principal adeles. Its descent uses the proved principal-map compatibility, the
additive block multiplication law and the fact that reducing a rational matrix
gives zero. Equality of the reduced coordinates implies that the two adelic
matrices differ by a rational matrix. The inverse rational coordinate
equivalence produces an actual rational subgroup point witnessing equality in
the original left quotient. Entrywise lifts of quotient matrices prove
surjectivity.

`quotientEquiv` is the resulting bijection. On quotient representatives it is
entrywise reduction of the actual coordinates. Its inverse on a reduced
adelic matrix is the original quotient projection of the inverse actual
coordinate map. `quotientHomeomorph` proves continuity in both directions
using the actual subgroup quotient topology, the coordinate homeomorphism
and the open quotient property of entrywise reduction. It uses no topology
on the rational field.

Positive right translation becomes addition of the reduced coordinates of the
translating point. Under the explicit original hypothesis
`CompactSpace (AdeleQuotient F)`, the actual subgroup rational quotient is
compact by this homeomorphism and finite matrix products. This is a conditional
specialization of additive quotient compactness, rather than a general
reductive reduction or finite-volume theorem.

All arguments derive from the existing actual-point and original matrix
definitions. This module constructs neither a quotient measure nor an integral
comparison. Those require further transport and normalization identities.
