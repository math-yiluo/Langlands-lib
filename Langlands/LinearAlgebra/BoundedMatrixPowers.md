# A finite matrix lattice and bounded powers

This internal construction is derived for the anisotropic spectral integrality
proof. For a commutative ring embedded in a field, `scaledMatrixLattice R b`
is the range of the coefficient inclusion on finite square matrices followed by
scalar multiplication by `b`. It is a finitely generated module, since the
standard matrix module over the coefficient ring is finite. Its membership
criterion records the corresponding entrywise equations.

Over a valuative field, an entrywise bound by a nonzero `b` places the matrix
in this lattice for the canonical valuation integer subring: divide every
entry by `b` to obtain an integral entry.

The general algebra lemma says that if all nonnegative powers of an algebra
element lie in a finitely generated module over a Noetherian commutative ring,
the element is integral. The algebra it generates is the module spanned by
these powers, so it is a submodule of that finite module and is itself finite.
The finite-algebra integrality theorem then applies. The ambient algebra may be
noncommutative.

Consequently a common bound on all entries of every nonnegative power of a
matrix makes that matrix integral over a Noetherian valuation ring. For a
nonarchimedean local field the valuation ring is a discrete valuation ring and
hence Noetherian. `IntegralMatrixCharpoly` gives integrality of each
characteristic-polynomial coefficient, and the valuation integer subring is
integrally closed inside the field; equivalently, each such coefficient has
value at most one. All finite index types, including the empty type, are allowed.
This helper proves no anisotropic group assertion or boundedness premise.
