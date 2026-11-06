# Locally constant actual geometric root profiles

This internal module fixes an actual map from a standard split torus into a
smooth affine group scheme over an arbitrary commutative ring. Neither
connectedness of the fibres nor a closed-immersion hypothesis on the torus
map is needed. Every fibre used here is the existing `geometricFiber G s`
over the chosen algebraic closure of the actual residue field.

The canonical torus factor into the actual geometric identity component has
the same adjoint character weight dimensions as the whole geometric fibre.
For the fixed-exponent character attached to an integer vector `m`,
`finrank_weight_geometricIdentityComponentHom` identifies that dimension
with the stalk rank of the actual relative exponent summand.

`geometricExponentRoots` expresses the actual roots of that torus map in the
common integer coordinates. Its membership criterion is precisely that the
integer vector is nonzero and the relative exponent rank is nonzero. The
proof uses finite dimensionality of the actual Lie algebra over the
geometric field: a character weight space is zero exactly when its dimension
is zero. The coordinate character equivalence detects the zero character.
The actual roots remain the existing nonzero characters with nonzero
all-test adjoint weight spaces.

The full root support is locally constant as a function to sets of integer
vectors. Moreover, one open neighbourhood of any base point simultaneously
preserves the full root support and every actual character weight dimension
in the geometric identity components. This follows from simultaneous local
constancy of the relative summand ranks, including the finite-support
argument already implemented in `RelativeAdjointWeightRanks`.

The provenance is internal: the proofs compose the existing actual
geometric-fibre weight comparison, the differential weight equivalence for
the actual identity-component inclusion, finite-dimensional linear algebra,
and the integral character-coordinate equivalence. This supplies root and
root-line preservation for the relative reductivity argument. It does not
construct Weyl elements or assert reductivity or openness of the reductive
locus.
