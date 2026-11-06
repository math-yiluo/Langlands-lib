# Haar regularity from actual finite-coordinate point topologies

Author: Worker 1650.

`rationalPointHaarRegularity` proves the unchanged
`RationalPointHaarRegularityStatement`.

The proof reuses the published
`Langlands.HarmonicAnalysis.GeneralLocalField.secondCountableTopology`.
That result equips the existing local-field topology with its compatible
uniform structure and with the norm from a rank-one valuation. Local
compactness makes this nontrivially normed field proper, so it is second
countable. These auxiliary structures preserve the existing field topology.

The published `affineSchemePointSecondCountability` proves second
countability for the finite-type affine scheme's ring-valued points.
The canonical `rationalPointHomeomorph` transfers this property to precisely
the identity-test rational-point carrier and topology.

The existing rational-point group results give a Hausdorff locally compact
topological group. Combined with second countability these yield a
metrizable, sigma-compact space. Each supplied Haar measure is locally
finite. Mathlib's regularity and inner-regularity instances now apply to its
Borel measurable structure. No change of the measure or normalization is
used.

The reused field theorem and the new rational-point theorem provide the
second-countability steps. This proof supplies only the topological and
measure regularity adapter; it supplies no algebraic-set nullness.
