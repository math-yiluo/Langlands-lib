# Congruence transport of general Hermitian matrix points

This is internal elementary matrix infrastructure, generalizing the construction
in `HermitianRootIsometryTransport` to arbitrary nonsingular Gram forms.
An actual invertible matrix `P` is a congruence from `H` to `J` when
`adjoint P * J.gram * P = H.gram`. The resulting group equivalence sends
`g` to `P * g * P⁻¹`. Its inverse uses `P⁻¹`; both matrix formulas are exposed.
The determinant of `P` is unrestricted.

The inverse congruence follows by multiplying the original equation on both
sides by inverse matrices. Associativity and this inverse equation prove
preservation under conjugation. Multiplicativity of determinant proves the
conjugated matrix still has determinant one. Applying an involution-compatible
coefficient homomorphism entrywise transports the congruence and commutes with
the point equivalence. These statements require only commutative rings,
finite indices and the specified involutions, including characteristic two.
No classification or decomposition theorem is used.
