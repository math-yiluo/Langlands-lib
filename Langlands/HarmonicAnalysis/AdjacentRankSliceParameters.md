# Exact parameters for the adjacent-rank affine slices

Worker 1198. Internal coordinate adapters for the complementary anti-triangular
slices of `AdjacentRankAffineFourier`. Strict upper positions `(i,j)` map to
`(i.rev,j)` in the right slice. In the left slice they map to `(i,n+1-j)`,
while an additional full row supplies the first column. These maps are proved
bijections, including when the square size is one and the strict upper set
is empty.

The measure statements use a field `K` with continuous ring operations, its
Borel measurable structure and second-countable topology, and a supplied
sigma-finite regular additive Haar `ν`. The left measure-preservation
theorem additionally assumes local compactness and the Hausdorff property,
which supply Haar invariance under negation. These coordinate results do
not require a character or scalar self-duality. The final matrix identities
retain the topological-ring and measurable structures needed by the
imported group-coordinate API; their arguments are entrywise algebra.

The parameter maps use the published coordinate-slice parameterization,
reindexing finite scalar products. The left parameters negate both the upper
coordinates and the row; scalar Haar negation invariance preserves their exact
product measure. Consequently both maps push forward exactly to the indicated
slice measures, with no normalization scalar.

The last two lemmas identify the resulting matrices entrywise. The right
parameter equals the actual long Weyl matrix times the original upper
unipotent. The left has first column minus the supplied row and its other
columns are the negatives of the original upper-unipotent columns in reversed
positive-column order. These are coordinate facts only: no actual group Haar
is equated to the coordinate product and no Fourier identity is assumed.
