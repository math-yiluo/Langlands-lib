# Finite local insertion in adelic general-linear coordinates

`GeneralLinearLocalInclusionComparisonStatement` fixes a number field
and a matrix size. Inserting a point in the general linear group over
a finite completion and applying the adelic matrix comparison agrees
with inserting its local matrix in the finite adelic matrix group and
then in the full adelic matrix group.

The affine-points comparison is natural for each projection from the
adele ring to a completion. At every infinite place the inserted group
point is the identity, so the infinite adelic matrix is the identity.
At the chosen finite place the projection is the given local matrix,
and at every other finite place it is the identity. These are exactly
the projections of the finite matrix insertion.

`adelicHomeomorph_ofPlace` supplies the compatibility needed when a
completed-local action on forms is compared with adelic right
translation on their quotient classes.
