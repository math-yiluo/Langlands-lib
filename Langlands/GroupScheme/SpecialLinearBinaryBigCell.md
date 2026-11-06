# The binary special-linear unit cell

This derived construction uses the actual upper-triangular subgroup of the
binary special linear group. Its Weyl point has matrix `[0,-1;1,0]` over the
original base ring. Conjugation has matrix `[d,-c;-b,a]`, so the conjugate
inclusion has exactly the lower-triangular matrices on every relative test
scheme.

If a determinant-one matrix has unit bottom-right entry `d`, set `t=d⁻¹c`.
The upper unipotent matrix with parameter `t` conjugates to the lower unipotent
with parameter `-t`. Multiplying the original matrix by that lower unipotent
kills its bottom-left entry, giving an upper-triangular matrix. Cancellation
then gives the original matrix as an upper factor times the inverse of a
conjugate upper factor. The actual matrix-point equivalences produce both
factors globally on the original relative test scheme. Tests may be nonaffine
or nonreduced, and the base is any commutative ring.

Over a field, the bottom-right entry is an actual affine coordinate obtained
from the published row-polynomial map. Its evaluations are the matrix entry
on every test. Left multiplication by the upper subgroup and right
multiplication by the inverse conjugate both scale it by the same
last-diagonal character coordinate. The entry equals one at the identity on
every test. Consequently its unit locus has the stated global inverse-factor
decomposition.

The provenance is elementary matrix multiplication, the explicit binary
inverse, the already constructed actual upper subgroup and character, and the
published all-test affine coordinate comparisons. The reused subgroup and row
coordinate constructions are by Worker 1369; this geometry construction is by
Worker 669. This result does not identify the entire covariant space, prove
irreducibility, or prove the general Steinberg big-cell proposition.
