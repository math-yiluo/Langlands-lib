# Original torus bounds from intrinsic root-Levi normalization

This internal auxiliary unit connects bounded central normalizations to torus
coordinates in the actual Levi–torus–unipotent order. It works over a number
field in an arbitrary universe. It does not prove the arithmetic rank-one
height assertion or construct positive coordinates.

`orbitHeight_normOne_mul_torus_mul_unipotent` removes the right unipotent
factor because its preserved coordinate line is fixed pointwise. Exact torus
line-character scaling and the intrinsic norm-one condition of the source
Levi remove the left factor from the selected-vector height.

`centralAdjustedTorusPoint_factorization_right_unipotent` commutes the
central adjusting point past the left Levi factor, cancels it against its
inverse in the torus, and retains the original factor order.
`centralAdjustedTorusPoint_mem_normOne_and_height_right_unipotent` then
uses subgroup closure to deduce intrinsic norm-one membership of the adjusted
torus image and the preceding exact height identity. No minimum inequality is
transported through a right fixed factor by these lemmas.

`HasBoundedRootLeviTorusAdjustment` records an actual torus point whose image
in the canonical singleton standard Levi is intrinsically norm one, whose
original simple-root norm is unchanged, and whose selected-vector height is
bounded by the specified real number.

`hasBoundedRootLeviTorusAdjustment_of_normalization` starts with the actual
inclusion of the original minimal Levi and a supplied intrinsic minimal
unipotent of the singleton Levi. It requires their line preservation,
unipotence, the actual relative-root condition in this Levi, and bounded
central normalization of their product with the original torus coordinate.
The closed singleton-Levi immersion cancels the recorded ambient composite
to identify the central torus factor intrinsically. The resulting central
adjustment preserves the root norm, is intrinsically norm one, and has height
at most `c * C`. The raw product is not assumed norm one.

`hasUniformRootBound_of_minimal_coordinates_and_prefix_minima` supplies the
structural hypotheses of the preceding theorem in the actual connected
reductive setup with maximal split torus and generic cocharacter. Choose a
valid family of standard parabolic indices, an index `l < r`, and an actual
simple root `α` omitted from index `K l` and contained in every preceding
index. The selected ambient representation must have that standard parabolic
as its exact coordinate-line stabilizer on every scheme test.

For every fixed `c > 0`, any family of original torus points occurring in
minimal Levi–torus–unipotent products satisfying the prescribed prefix
minimum inequalities with constant `c` has one uniform upper bound on the
normalized norm of `α`. The original minimal-Levi factors are intrinsically
norm one. No positivity or ambient norm-one condition is imposed on the
torus family or on its raw products.

The proof identifies the singleton Levi's intrinsic simple roots with
`{α}` and the exact restricted line stabilizer with its intrinsic minimal
parabolic. The published positive integral root-character relation applies
to that same restricted representation; it retains the Levi-character
term until intrinsic norm-one membership removes it. The original minimal
Levi preserves the line because it lies in `P_(K l)`, and the intrinsic
minimal unipotent is proved unipotent and fixes the line vector.

The explicitly supplied universal rank-one arithmetic assertion gives a
positive bound `C` for bounded central normalizations, uniformly before the
torus points are chosen. Actual minimal-coordinate decomposition constructs
the raw singleton-Levi and outer-unipotent factors. Its normalization
therefore supplies root-preserving, intrinsically norm-one torus adjustments
of height at most `c * C`. The existing uniform adjustment comparison yields
the promised original-root bound. The adjusting central torus may depend on
the original point; the bound does not.

The provenance is derived from actual standard-Levi coordinates, the central
normalization predicate, central-root restriction, the rank-one positive
line-character relation, and adelic line-height identities in the Library.
The arithmetic assertion is a premise, not a proved input. Constructing
positive coordinates and assembling simultaneous root bounds into the full
chamber-reduction theorem remain separate obligations.
