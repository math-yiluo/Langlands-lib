# Actual representations on the fixed space of a normal subgroup

Worker 1228.

This internal construction restricts an actual finite matrix representation to
the full fixed subspace of a normal affine subgroup. It also computes the
scheme-theoretic kernel under an explicit fixed-vector stabilizer hypothesis.

The finite split coordinate construction `exists_subspace_split_coordinates` uses a basis of the actual fixed
submodule and a linear retraction onto that submodule. Normality gives stability
via the published coefficient-extraction argument in `NormalFixedCoordinates`.
The published `restrictCoordinates` then constructs the actual homomorphism of
group schemes, retaining its intertwining law on every test scheme. The subgroup
acts trivially because each column of the coordinate inclusion is fixed.

If an original subgroup-fixed vector has stabilizer contained in the subgroup's
range on all tests, a point in the new representation's kernel fixes that vector,
so it belongs to the subgroup. Conversely every subgroup point acts trivially.
`range_kernel_eq` expresses this as equality of the actual represented kernel
range and the prescribed subgroup range.

The construction works over an arbitrary field and imposes no smoothness,
connectedness, or characteristic restriction. It does not construct the original
fixed vector or prove that normality supplies the stabilizer hypothesis, and it
does not construct an affine quotient. Its provenance is an internal derivation
from the published normal fixed-coordinate stability and split-coordinate
restriction interfaces and Mathlib's finite-dimensional linear algebra.
