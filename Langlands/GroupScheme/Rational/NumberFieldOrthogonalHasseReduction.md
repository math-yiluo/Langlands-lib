# The orthogonal Hasse principle reduces to quadratic isometry

`NumberFieldOrthogonalGaloisHasseStatement` restricts the finite-Galois form
of the number-field Hasse principle to group schemes isomorphic to the
orthogonal group of a nondegenerate scalar quadratic form. It includes every
number field, form dimension and finite Galois extension in the stated
universe. Two cocycles are compared by a cochain on the actual cover, with
the same cohomology relation on its pullback to every completion.

`numberFieldOrthogonalGaloisHasse_of_quadratic` proves this implication from
`Langlands.NumberFieldQuadraticIsometryStatement`. First it transports the
cocycles along the supplied group isomorphism. Mapping their values commutes
with base change, so their local cohomology transports as well. The polar
matrix chart and Hilbert 90 then associate two symmetric invertible Gram
matrices over the number field to the transported cocycles.

For each finite or archimedean completion, the cochain on the pullback
cover gives a matrix twist over the coefficient tensor ring. Fixed
coefficient descent gives a congruence of the two Gram matrices over the
completion. The quadratic-isometry hypothesis, through its Gram-matrix
comparison, supplies a congruence over the number field. This yields a
matrix cochain, lifts to a natural cochain on the Galois cover, and
transports back along the inverse group isomorphism.

This internal reduction combines the Library's natural cocycle operations
with the scalar orthogonal and Gram comparisons. The arithmetic premise is
the classical local-to-global isometry theorem. The parent finite-Galois
reduction supplies the passage to finite separable covers when the three
group cases are assembled.
