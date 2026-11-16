# Matrix descriptions of split-torus families on open neighbourhoods

This internal module extends the published all-test split-torus family
interface from an entire parameter scheme to a supplied parameter subtest.
If one integer matrix describes the family at every residue-field point of
that subtest, it describes the family on every relative test over it.

The proof works on affine charts. The grouplike coefficients are idempotents;
pointwise equality makes each required coefficient a unit, hence equal to one.
The published coefficient criterion then gives the full family equation.

The existing local constancy of exponent matrices supplies an open
neighbourhood of each parameter point with a fixed matrix description.
`matrixNeighbourhood` chooses that neighbourhood and matrix together with the
all-test property. No connectedness, affineness or quasi-compactness assumption
is made on the parameter scheme. Distinct neighbourhoods may use different
matrices. This supports local root-data transport in geometric pinning
normalization and does not assert that normalization itself exists.
