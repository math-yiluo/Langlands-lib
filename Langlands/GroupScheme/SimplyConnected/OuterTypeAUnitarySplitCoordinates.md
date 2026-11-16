# Hermitian coordinates from unitary splitting

This internal derivation removes the distinguished-endpoint premise from the
existing Hermitian coordinate extraction when the base field has the unitary
involution splitting property. It uses the actual quadratic star field,
cover discrepancies, and all-test diagonal split-torus characters.

The inner subgroup is the subgroup fixing the star field. The published
mixed-discrepancy theorem gives its twisted projective cocycle. Unitary
splitting makes this cocycle scalar after a change of coordinates. The
new torus-preserving correction replaces that change by one retaining all
diagonal characters. The published Hermitian outer-representative theorem
then gives a nonsingular Hermitian form on the star field, trivial inner
discrepancies, and the required Hermitian outer discrepancy for every
automorphism moving the star field. All torus coordinates are retained.

This auxiliary result does not yet prove the exact distinguished vertices
or the local rank-one enumeration.

`TypeAHermitianTorusCoordinates L d e` packages a nonsingular Hermitian
form, its full natural all-test presentation, the original diagonal
split-torus characters, and their differences giving every simple-root
restriction in the supplied numbering. The presentation is an equivalence
onto all determinant-one isometries on every test scheme.

For a simply connected absolutely almost-simple group with every Cartan
entry of type A and full star image equal to identity or chain reversal,
unitary splitting constructs these coordinates on the actual quadratic
star field. The proof uses the published special-linear Tits cocycle,
retains its torus and root coordinates, applies the correction above,
and descends the resulting Hermitian discrepancies. It then packages the
unchanged matrix values using the published `ofMatrixPoints` constructor.
`hermitianTorusCoordinatesOfUnitarySplitting` chooses this actual presentation.
There is no rank-one or endpoint assumption. All universes and field
characteristics are retained. The full star action is still the original
one defining the star field, rather than a replacement action.
