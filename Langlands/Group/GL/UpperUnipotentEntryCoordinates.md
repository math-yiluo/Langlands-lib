# Actual scalar entry coordinates for upper-unipotent Haar integration

Author: Worker 623.

This internally derived helper makes the scalar entry coordinates of the
actual upper-unipotent group explicit. It applies over a locally compact,
Hausdorff, second countable topological field with its Borel measurable
space and a supplied sigma-finite additive Haar measure. It does not choose
a new normalization for that scalar measure.

`UpperEntryPair d` consists of pairs of indices `i<j` in a `d` by `d` matrix.
`upperEntryCoordinates d` is a homeomorphism from the published actual
upper-unipotent group to scalar families on these positions. It reads the
actual matrix entries. Its inverse is the upper-unipotent matrix with
these entries, diagonal one and entries below the diagonal zero. The
construction specializes the published radical coordinates to the singleton
block shape and evaluates its one by one blocks. It is a homeomorphism of
spaces, not a homomorphism to the pointwise additive coordinate group.

`upperEntryCoordinates_mul` states the triangular multiplication formula

```text
(uv)_ij = u_ij + v_ij + sum_(i<k<j) u_ik v_kj.
```

`upperEntryProductMeasure ν d` is the product of the supplied scalar Haar
measure over all strictly upper positions. `upperEntry_leftTranslation_preserving`
proves that left multiplication in the actual group, expressed in these
coordinates, preserves this product. The correction in coordinate `(i,j)`
depends only on coordinates of smaller distance `j-i`, so the published
finite triangular translation theorem applies.

`upperEntryProductMeasure_isHaar` then proves that pushing the product
through the inverse coordinates gives Haar measure on the actual group.
`exists_upperEntry_integral` compares every supplied group Haar measure
with this product: it supplies a positive real factor `c` such that, for
every complex-valued function, its group integral is `c` times the integral
of its coordinate pullback. The same factor applies to every function;
it is not claimed to be one. Empty coordinate sets, including dimensions
zero and one, are allowed.

The proof uses the published singleton-block identification and radical
coordinate multiplication theorem, finite triangular translation invariance,
and Haar uniqueness. This is internal provenance. No Fourier slice,
Whittaker pushforward comparison or gamma equation is asserted here.
