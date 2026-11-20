# Fixed block flags of normal real matrices

`RealCartanFixedFlagStatement` applies to a real matrix `C` with source
slots given by the fibers of `a`. Each slot has at most two indices.
Entries between slots vanish, and the two off-diagonal entries of each
two-index slot are nonzero and opposite. The matrix is normal, and
`C * Cᵀ` is diagonal with entries constant in each slot and distinct
across slots. The target blocks are the fibers of the ordered label
map `b`.

Suppose `Q` is orthogonal and `Q * C * Qᵀ` is upper triangular by target
blocks. Then there is a permutation `π` matching source columns to target
rows. All indices `i` of a source slot have the same target label `b (π i)`.
The entries in column `i` of `Q` outside that target block vanish.

The proof first compares the sum of squared row and column norms across
each cut in the ordered target blocks. Normality gives equal norms for
each row and its corresponding column. Terms with both indices on the
same included side of the cut cancel by exchanging indices. The entries
below the cut vanish by upper triangularity, so the sum of squares of
the entries above the cut is zero as well.

Consequently each coordinate projection onto a target block commutes
with `Q * C * Qᵀ`. Transporting the projection by `Qᵀ` gives a symmetric
matrix commuting with `C` and with its transpose. Commutation with
`C * Cᵀ` forces zero entries between source slots. In a two-index slot,
the two sides of a diagonal entry of the commutation equation use
opposite nonzero off-diagonal entries of `C`. Symmetry then forces the
off-diagonal entries of the transported projection to vanish. The
off-diagonal commutation equation equates the two diagonal entries of
the transported projection. Each transported projection is therefore
diagonal and constant on each source slot.

The determinant expansion for `Q` supplies a permutation with a nonzero
entry in each matched row and column. At any nonzero entry in column `i`
of `Q`, the diagonal entry of the transported projection equals the
indicator of membership of that row in the target block. Comparing
these indicators with those in the matched rows proves both claims
about `π`.

This is an internal matrix calculation for the fixed block flags of
regular real Cartan elements. The hypotheses on `C` describe signed
scalar slots and scaled rotation slots with distinct radii and nonzero
rotation sines.
