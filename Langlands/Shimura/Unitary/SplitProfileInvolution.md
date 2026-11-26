# An involution on the algebra of a signed split profile

`exists_csa_with_involution_for_splitProfile` gives the prescribed degree
and signed Brauer invariants together with a unitary involution inducing
the specified scalar conjugation. It imposes no further local type on
that involution. `SecondKindInvolution.ofUnitaryInvolution` expresses the
resulting semilinear map as a linear algebra involution over the real
field.

Place the prescribed values on the chosen upper places and set the other
values to zero. At an auxiliary nonsplit finite place, add the negative
of the sum. The auxiliary place above it is unique by the quadratic
degree bound and is fixed by conjugation. The balanced profile is
realized by a central simple algebra. Tensor that algebra with its
conjugate opposite and use the factor exchange involution. The invariant
of this tensor is the difference between the balanced profile and its
conjugate. The auxiliary correction cancels, and the two places above
each selected split place acquire the two prescribed opposite values.

The finite invariants determine the Brauer class over the totally
complex field. The degree-prescribed representative of the signed
profile therefore carries a unitary involution by matrix-stable transfer.
