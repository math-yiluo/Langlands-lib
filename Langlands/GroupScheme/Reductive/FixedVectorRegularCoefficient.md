# A fixed vector and the constant regular function

This is a derived construction for an actual group functor corepresented by a
commutative algebra `B` over a field `k : Type u`. It uses the Library's universal
representation coefficients, finite regular subspaces and their actual matrix
representations. It requires no reductivity, characteristic or smoothness
assumption.

For a representation `ρ`, a vector `v` and an index `i`,
`normalizedCoefficientFamily` is the family
`a j = (v i)⁻¹ • N i j`, where `N` is the universal matrix of `ρ`.
The family satisfies the same row-coaction identity as the coefficients of `ρ`.
If `v` is fixed over every test scheme and `v i` is nonzero, its coefficient
combination `∑ j, v j • a j` is the constant function `1`. The proof evaluates
fixedness at the universal affine point, then multiplies its `i`th row equation
by `(v i)⁻¹`.

`exists_finite_regular_map_to_one` chooses an index with `v i ≠ 0`, takes the
finite regular span of this family and chooses its finite basis `b`. The matrix
whose columns are the basis coordinates of `a j` intertwines the supplied
representation with the actual regular-subspace representation.
Its value at `v`, expanded in `b`, equals `1` in `B`. The proof uses the
coaction equation to obtain equivariance and interchanges two finite sums to
reconstruct the regular function at `v`.

The imported `Intertwines` tests every commutative coefficient algebra,
including nonreduced algebras. The regular representation follows the imported
right-translation convention. The conclusion is a map into one finite regular
subspace, rather than an injection of the whole source representation into one
coordinate ring.

This algebraic construction is motivated by the coordinate-ring step of the
Haboush proof sketch in Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*,
third enlarged edition (1994), Appendix 1.A, printed p.192. Its proof here is
derived directly from the imported coefficient and finite-regular-span APIs.
It does not construct Steinberg modules, identify coordinate-ring subspaces
with their endomorphisms, or prove geometric reductivity. Passing from a
general affine group scheme to the supplied corepresented presentation remains
a separate adapter.
