# Finite spectral support from integral operators

This internal linear algebra module concerns two complex vector spaces in
independent universes and integral endomorphisms on them. The spaces need not
be finite dimensional. The construction maps the tensor product of
endomorphism algebras to the endomorphism algebra of the tensor product. The
single-operator subalgebras are finite because the operators are integral;
their tensor product is finite, and integrality passes through the action map.

A polynomial induction shows that a functional covariant under an operator
is covariant under every polynomial in it, with scalar given by polynomial
evaluation. Apply this to the linear functional on the tensor product associated
to any bilinear form. A fixed monic annihilator of the tensor operator forces
all covariance scalars of nonzero forms into its finite root set. The finite
set is chosen before the scalar and the bilinear form. Zero carriers are allowed.

`powerSpectralExceptions` is the finite union, over the original exceptional
scalars c, of roots of X^m - c. For positive m these polynomials are nonzero,
so avoidance of the new set implies that the m-th power avoids the original
set. `exists_finite_bilinear_power_spectral_support` therefore gives a finite
exceptional set for a parameter whose m-th power is the covariance scalar.
The positivity requirement is explicit; no injectivity of complex powers is
assumed. This covers the positive matrix rank needed in the later application.

This is an internal prerequisite for the central residual term of equal-rank
trilinear uniqueness. It does not assert that any particular representation
operator is integral or identify its scalar with a Rankin–Selberg spectral
parameter. The proof uses Mathlib tensor products, finite algebras, integrality,
and polynomial roots, without a representation-theoretic classification.
