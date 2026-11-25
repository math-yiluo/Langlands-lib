# One convergent finite approximation on the original ambient and cusp spaces

`groupSchemeFullAEL2FiniteApproximation` proves
`GroupSchemeFullAEL2FiniteApproximationStatement` at universe `u`. This internal
proof uses the
original Haar quotient measure and the full all-parabolic almost-everywhere
cuspidal submodule.

The published `groupSchemeQuotientL2FiniteApproximation` supplies one antitone
identity basis of compact open subgroups of the finite adelic group, together
with fixedness, strong convergence and finite smooth-vector density on the
ambient space. At each index, the ambient and cusp averages use the normalized
Haar probability measure of the same subgroup.
`fullAEL2CuspidalFiniteAverage_val` identifies the included cusp average with
the ambient average of the included vector.

The cusp space inherits its topology and norm from the ambient `L²` space.
The proof applies `tendsto_subtype_rng` and rewrites the included averages using
the value identity to obtain strong convergence on the cusp space.
`fullAEL2CuspidalFiniteAverage_mem_fixedVectors` gives fixedness under the
subgroup at each index for the original finite cusp action. That subgroup
witnesses finite smoothness, and `mem_closure_of_tendsto` puts each cusp vector
in the closure of the finite smooth vectors.

`fullAEL2CuspidalOrthogonalProjection_finiteAverage` gives the intertwining
identity for the subtype-valued orthogonal projection.
`fullAEL2CuspidalAmbientProjection_finiteAverage` gives commutation with the
ambient cusp projection.
