# Torus coordinates for a proper padded block

This internal helper supplies the algebra of the torus coordinates used in
the proper-block gauge integral. For a diagonal tuple
`d = (d₀, …, dₜ)`, its coordinates are
`(d₀ / d₁, …, dₜ₋₁ / dₜ, dₜ)`. The inverse multiplies all coordinates at
or after each index. Both inverse identities are proved over any commutative
group, and `blockRootEquiv` records the resulting multiplicative equivalence.

The proof of the inverse identities splits off the first factor of each
inclusive tail product and uses reverse induction on the index. Reordering
the product of all tail products shows that the coordinate with index `j`
occurs `j + 1` times. Specializing this identity to ideles and applying the
normalized idelic absolute value gives
`detNorm(diag(d)) = ∏ j, |aⱼ|^(j + 1)`.

The coordinate map is also a continuous multiplicative equivalence.
For a locally compact, second countable topological commutative group,
`lintegral_blockRoots_lt_top_iff` proves that the coordinate change
preserves finiteness for every Haar normalization on the finite product.
The transported measure is Haar and thus is a positive finite constant
times the original Haar measure. The proof makes no assertion that this
constant equals one.

The provenance is finite commutative-group algebra and the Library's actual
diagonal matrix and determinant norm definitions. This file supplies no
integration formula for the Whittaker quotient or convergence assertion.
Its gauge definitions are imported from the Library.
