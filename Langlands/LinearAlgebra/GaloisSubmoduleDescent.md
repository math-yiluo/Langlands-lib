# Infinite-Galois descent of coefficient-stable subspaces

This internal linear algebra construction is derived from Mathlib's fixed-field
theorem for an arbitrary Galois extension. The fields may have arbitrary
characteristic, and the extension need not be finite. The coordinate index type
has an independent universe and may be infinite; every individual vector is
finitely supported.

`extend` is the ground-field linear map that extends each coefficient via the
field algebra map. `conjugate` applies a ground-field automorphism to each
extension-field coefficient.

A subspace of the extension-field coordinate space is assumed stable under every
ground-field automorphism acting on coefficients. The proof first takes a
nonzero vector with smallest support inside the support of a given nonzero
vector. Normalize one nonzero coordinate to one. Subtracting any conjugate gives
a vector with smaller support, so minimality makes every such difference zero.
The infinite-Galois fixed-field theorem then descends each coefficient.

Induction on support size eliminates one coordinate at a time with these fixed
vectors. It proves that the original subspace is the extension-field span of
its vectors with coefficients in the ground field. This file does not by itself
construct descent of a scheme or closed subgroup; it supplies the linear algebra
step for invariant coordinate ideals.
