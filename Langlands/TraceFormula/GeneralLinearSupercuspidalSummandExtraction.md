# Extracting a cuspidal summand with the prescribed local types

`extract_supercuspidalSummand_of_determinantUnitOccurrence` takes a dense
family of irreducible closed invariant subspaces of the actual cuspidal
Hilbert space. It also takes one nonzero vector fixed by the integral
subgroups outside the specified places. At each prescribed place the
vector belongs to the range of a linear map that intertwines the action
of matrices of determinant valuation one.

Density gives a summand with nonzero projection of the common vector.
The orthogonal projection intertwines all translations because each
translation is an isometry preserving the summand in both directions.
The projected vector therefore has the same fixed subgroup. All of the
projected local maps are nonzero since their ranges contain that vector.

A scalar local matrix inserts into the center of the actual adelic group.
The unitary Schur hypothesis makes its action on the selected summand a
scalar. The cyclic-quotient argument upgrades each determinant-unit
intertwiner to an intertwiner for an unramified determinant twist. This
leaves the original summand and the same common fixed vector in place.
