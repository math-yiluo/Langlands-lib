# Constant outer-isomorphism charts for pinned split reductive models

`Langlands.GroupScheme.pinnedOuterIsomorphismChart` proves exactly
`Langlands.GroupScheme.PinnedOuterIsomorphismChartStatement.{u}` for every
universe `u`.

The implemented proof applies the published
`pinnedOuterIsomorphismChart_of_pinnedTheorems` and discharges both of its
inputs using published results:

1. `affinePinnedIsomorphismTheorem_of_unpinned` applied to
   `affineSplitIsomorphismTheorem` supplies the full affine pinned isomorphism
   theorem over every commutative ring.
2. `AffinePinnedModel.hasFppfLocalPinnedRepresentatives` supplies an
   fppf-local pinned representative of each actual comparison between the
   supplied models over any common scheme.

The chart construction uses the full character-lattice comparison labels
`AffinePinnedModel.ComparisonLabel M N`. Their canonical representatives
form an actual natural family over the scheme coproduct of copies of the
common base. The affine pinned theorem proves local completeness of those
representatives. Zariski and fppf descent classify each normalized comparison
by a unique morphism to that constant scheme on the original test. Natural
normalization and the full-centre quotient give the unique adjoint coordinate
on the same test. Classifying the family in the arbitrary supplied Isom
representative transfers this orbit bijection to the exact target, with the
inverse-precomposition action specified there.

Consequently the theorem retains every supplied pair of affine pinned
models, common base, full-centre adjoint quotient and all-test Isom
representative. Tests may be nonaffine, nonreduced, disconnected or empty.
Labels may vary locally, and their indexing type may be empty or infinite.
The proof has no additional premises.

This is an internal composite proof of the Library's derived pair statement.
Its mathematical provenance is the pinned classification and all-test
splitting described in the target's Markdown. The implemented route is the
published affine reduction, representation-free constant family, descent and
normalization assembly detailed above.
