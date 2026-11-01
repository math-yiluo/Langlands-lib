# Integral ideals and exact-dimensional ample section cokernels

`IntegralSupportDimensionStatement` specifies three internal support comparisons
for actual scheme-module sheaves in arbitrary universe `u`.

A nonzero ideal is an actual monomorphism into the structure module on an
integral scheme. Its closed stalk support is the whole scheme, and its support
dimension is the topological Krull dimension of that scheme. No coherence or
Noetherian assumption is imposed in this clause.

For a line bundle on an integral scheme and an actual global section whose
entire generation open is nonempty, the categorical cokernel of its section
morphism has support dimension equal to the dimension of the complement of
that generation open, with the induced subspace topology.

Finally, on an integral locally Noetherian scheme of finite dimension `d + 1`,
an ample line bundle has a positive tensor-power section with nonempty
generation open whose categorical cokernel is quasi-coherent, has finite
sections on every affine open, and has support dimension exactly `d`.
Here `d` can be zero; dimensions take values in `WithBot ℕ∞`.

These are derived interfaces for the Euler-polynomial positivity induction.
Their provenance is the actual unit locus of a nonzero ideal, density of a
nonempty open in an irreducible space, actual section-cokernel stalk support,
and an ample section cut of exact codimension one. The statement introduces
no support or positivity certificates and asserts no Euler-polynomial result.
