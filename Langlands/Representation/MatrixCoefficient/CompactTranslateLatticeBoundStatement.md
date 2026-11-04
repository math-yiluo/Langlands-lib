# Product coefficient bounds on compact translates of a lattice

Author: Worker 19.

`CompactTranslateLatticeBoundStatement` is an internal analytic adapter for a
smooth complex representation of any topological group. The field of scalars
is complex, while the group, representation carrier and finite coordinate
type have independent universes. The carrier has no topology. The lattice
map is an arbitrary function from the finite natural orthant to the group;
no homomorphism property is needed in this adapter.

The premise gives a product exponential bound for every vector and every
smooth-dual functional on that map. All these bounds use the same coordinate
weights `w`; their positive radii and constants may depend on the vector and
functional. Each squared radius times its weight is strictly below one.

For any two compact subsets and any finite middle subset of the group, the
conclusion gives a single such bound for each original vector and functional,
uniformly over all points `k₁ * τ(n) * t * k₂` with the three translates in the
specified subsets. The constant and radii may also depend on these subsets.
The coordinate type and all three translating sets may be empty. No
nonnegativity assumption on the weights is needed for this finite maximum
argument; actual volume applications supply positive weights separately.

The internal derivation uses
`JacquetCartanDatum.finite_image_of_isCompact` for the original smooth
representation and its smooth contragredient. The right compact product
`T * S₂` moves the vector to finitely many vectors; the inverses of `S₁` move
the functional to finitely many smooth functionals. Include the original
vector and functional to make these finite indexing sets nonempty. Apply the
premise to all pairs and take coordinatewise finite maxima of the radii and
a finite maximum of the constants. Every maximum is attained, so positivity
and every strict weighted gap remain true. Monotonicity of natural powers
and finite products gives the uniform estimate.

This is a derived intermediate statement, not an external literature theorem.
It assumes the untransformed coefficient estimates and does not prove their
spectral or geometric prerequisites. In the general rational Jacquet
criterion these estimates must first be proved from admissibility, the
actual strict exponents and the simultaneous contraction basis. The adapter
supplies no Cartan cover, basis existence, quotient volume bound or
integrability result. It invokes no classification, geometric lemma,
adjointness, character independence or cuspidal-support theorem.
