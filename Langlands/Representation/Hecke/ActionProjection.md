# Actual Hecke fixed-vector projections

For a Haar measure and a compact open subgroup `K`, the actual normalized
indicator `HeckeAlgebra.normalizedIndicator μ K hK` acts by a projection with
image exactly the existing `Langlands.fixedVectors ρ K.toSubgroup`. The
normalization is the inverse complex scalar of the positive finite real Haar
mass of `K`.

The formula on a fixed vector follows from the finite-fiber integral of a
constant indicator. Left invariance of the test function forces the image into
the fixed subspace by the left translation identity. These two facts give the
range equality and a linear retraction `fixedProjection` into the existing
submodule. Idempotence also follows directly from convolution multiplicativity
and the actual convolution idempotence of the normalized indicator.

The naturality theorem uses `fixedVectorsMap`, the published restriction of
representation intertwiners. When `J ≤ K`, both composites of the J and K
averaging operators equal the K averaging operator; these identities follow by
applying the actual Hecke action to the normalized-indicator refinement
identities.

Local units and nondegeneracy under the Hausdorff locally compact totally
disconnected hypotheses are developed separately in `ActionLocalUnits`.
This projection construction takes a compact open subgroup as input and needs
only a topological group with its Borel measurable structure and a Haar measure.

These are intrinsic laws of the actual integration construction, with no
topology or finite-dimensionality imposed on the representation carrier and
independent group and vector-space universes. The provenance is internal,
motivated by the natural Hecke module of Flath, section 1, printed page 179
(`flath-1979-tensor-products`).

The construction imports the published integrated action and normalized indicator.
The unital corner module is a subsequent construction; it is not asserted here.
