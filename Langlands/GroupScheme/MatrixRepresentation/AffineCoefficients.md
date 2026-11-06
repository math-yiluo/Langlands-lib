# Linear coefficients of the universal affine representation matrix

This internal construction uses the original finite matrix representation of a
supplied affine group scheme over a field. `coefficientMap` applies a ground-field
linear functional entrywise to its matrix at the universal affine point. The
coordinate algebra and test points are the existing actual objects.

`universalCharacterMatrix_map` evaluates that universal matrix at any affine test
point, by naturality. `universalCharacterMatrix_origin` evaluates it at the group
identity and obtains the identity matrix. `coefficientMap_mulVec` commutes
coefficient extraction with multiplication by a constant vector.
`isStableSubspace_iff` identifies all-affine-test stability with invariance under
every universal coefficient matrix. The reverse implication composes each
test-algebra functional with the coordinate map of its point, so arbitrary
nonreduced test algebras are included.

Every rational-point matrix lies in the range of `coefficientMap`, by its actual
base-field affine test. Over an algebraically closed field, when the ambient
scheme is reduced and locally of finite type, actual irreducibility gives
rational irreducibility. The existing Burnside matrix-span theorem then shows
that `coefficientMap` is surjective.

`coefficientSpace` is the span of the finitely many universal matrix entries.
For a Noetherian domain coordinate algebra and a supplied proper ideal `I`,
`exists_quotient_coefficients` applies ideal-power coefficient separation to
this finite-dimensional space. One exponent, chosen before every linear
functional, recovers its whole coefficient matrix from the quotient by `I^N`.
`exists_quotient_surjective` combines this with coefficient surjectivity: at one
quotient every matrix on the original coordinate space is obtained from a
linear functional on that quotient.

The provenance is the internal derivation described above from naturality,
all-test stability, rational irreducibility, the existing Burnside result and
ideal-power separation. The proper ideal and coordinate-ring domain and
Noetherian hypotheses remain explicit here. This unit does not prove tensor
irreducibility or construct highest-weight representations, induced-space
comparisons or big-cell data.
