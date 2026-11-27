# Base change of the discriminant with a quadratic field center

Consider compatible towers with maps \(F\to F'\), \(L\to L'\), and
\(M\to M'\), where \(L/F\) and \(L'/F'\) are quadratic and \(M/F\) is normal.
Start with a matrix splitting chart over \(M\) for a degree-\(2m\) central
simple algebra \(A\) over \(L\). The unitary involutions on \(A\) and
\(L'\otimes_L A\) induce the respective nontrivial center automorphisms,
which intertwine on \(L\). The involution on \(L'\otimes_L A\) agrees with the
original involution on \(1\otimes A\). The fields and algebras have a common
universe.

`relativeDiscriminantClass_baseChange` computes the class in the extended
matrix chart. Normality gives a restriction map from
\(\operatorname{Gal}(M'/F')\) to \(\operatorname{Gal}(M/F)\). The subgroup
fixing \(L'\) is the pullback of the subgroup fixing \(L\) along this map.
For the converse implication, an outer automorphism of \(L'\) acts on
the embedded \(L\) by its nontrivial automorphism, so it cannot fix all
of \(L\). Entrywise extension of the original lifts therefore uses the
correct cosets. Its action on simple tensors agrees with the extended
involution, since the action on \(1\otimes A\) and on scalar multiples
determines the semilinear action. The coefficient transfer of the
determinant factor set then computes the class by inflation and
restriction.

When the splitting fields are finite Galois over their respective base
fields, `scalarExtension_discriminantClass_baseChange` upgrades the same
identity to the algebraic Brauer groups. The ordinary relative Brauer
comparison computes the class of the extended regular representative
in its scalar-extended matrix chart.
