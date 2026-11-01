# Normed compact-restriction coordinates

This internal helper sends a continuous function to its restrictions to all
compact subsets of its domain. Each restriction has the supremum norm,
including restrictions to the empty set.

`tendsto_compactRestrictionCoordinates_iff` identifies convergence in these
coordinates with convergence in the compact-open topology, using uniform
convergence on every compact set. Singleton restrictions detect equality.
Consequently `isEmbedding_compactRestrictionCoordinates` proves that these
coordinates form a linear topological embedding into a product of normed
spaces.

The construction is internally derived from the imported Mathlib
compact-open topology and compact restriction results. It is a helper for the
scalar orbit-coefficient proof, not a claim of orbit smoothness,
density or reproduction.
