# Local dimension under flat open spectrum maps

This module proves an internal prerequisite for the base-change comparison
of local fibre dimension in Stacks Lemma 29.29.3(1). Worker 105 wrote the
proof; Worker 1604 checked and prepared it for publication.

The local dimension is the minimum of dimensions of open neighbourhoods,
as defined in `LocalTopologicalDimension`, with values in `WithBot ℕ∞`.
For any commutative ring A and prime q, `exists_away_dimension_eq_at`
finds an element r outside q for which the dimension of A[1/r] is the local
dimension at q. Start with a minimizing open neighbourhood and choose a
basic open D(r) inside it containing q. Subspace dimension monotonicity and
the defining local-dimension bound make both dimensions equal. The actual
localization-spectrum homeomorphism then identifies the dimension with
that of A[1/r]. No finite-type or Noetherian hypothesis is used.

`ringKrullDim_away_le_of_basicOpen_subset_range` treats an algebra R → S
satisfying going down. If D(r) is contained in the image of Spec S → Spec R,
then `ringKrullDim (Localization.Away r) ≤ ringKrullDim S`. A finite strict
chain in Spec R[1/r] contracts to a strict chain in Spec R because the
localization map on spectra is an injective order-preserving map. Its last
point lies in D(r), so the image hypothesis supplies a prime of S over it.
Mathlib's `Ideal.exists_ltSeries_of_hasGoingDown` lifts the entire chain
with its length unchanged. Taking the supremum of lengths proves the
bound. The rings may occupy independent universes.

For a flat algebra map whose actual spectrum contraction is open, choose
a principal source neighbourhood realizing local dimension. Its open image
contains the contracted point, so it contains a principal neighbourhood
there. The preceding chain comparison proves that the local dimension at
the contracted point is bounded by the local dimension at the source point.
Flatness is used for going down after principal localization. The resulting
theorem is `topologicalKrullDimAt_comap_le_of_flat_of_isOpenMap`; it retains
both flatness and openness as hypotheses.

The registered Stacks source is
`stacks-fibre-constructibility-local-dimension-2026-11-04`,
SHA-256 `1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
files `0055.html`, Definition 5.10.1, and `02FW.html`, Lemma 29.29.3(1).
The chain argument is an internal proof route supporting that affine
base-change result. This helper module does not prove the reverse
inequality for a field extension, the general scheme comparison or
retrocompactness.
