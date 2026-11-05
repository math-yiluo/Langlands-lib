# Vector factors of additive polynomial kernels

This internal construction iterates the actual one-coordinate product splitting
in `PolynomialKernelProduct`. It concerns explicit separated additive polynomial
rows over every field. It does not assume that an arbitrary unipotent group has
such a presentation.

`VectorGroup.zero_points_ext` proves that every two points of the
zero-dimensional vector group on any relative scheme test agree, by the empty
coordinate family. `VectorGroup.zeroProductIso` uses this uniqueness and the
product projections to identify its product with any group scheme with the
second factor. The inverse pairs the zero homomorphism with the identity.

`hasConstantAffineLineMaps_polynomialKernel_zero` applies the monomorphism from
the kernel to the zero-dimensional ambient vector group. Every affine-line
morphism equals the constant morphism through the kernel's identity section,
because their composites into that ambient group agree.

`exists_polynomialKernelVectorFactor` proceeds by induction on the number `n`
of row entries. If the kernel already has only constant affine-line maps, it
takes a zero-dimensional vector factor and leaves the row unchanged. Otherwise
the existing actual factor-extraction theorem splits off a one-dimensional
vector group and replaces the row by one with `n-1` entries. Induction gives a
constant-map polynomial-kernel complement. The monoidal associator and the
inverse of `VectorGroup.splitIso` combine the two vector factors. The result
includes the equality `r + m = n`, where `r` is the vector-factor dimension and
`m` is the remaining row length.

All isomorphisms are in the category of actual group schemes, and affine-line
constancy quantifies over actual affine-line scheme morphisms. No smoothness,
connectedness, perfection, infinitude, or characteristic hypothesis is used.
The arbitrary-group presentation and the full woundness criterion remain
separate obligations.
