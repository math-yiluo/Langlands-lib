# The actual permutation atlas of a supplied Borel adjoint torus

This is an internal construction from the supplied Borel charts and their
actual field comparisons, successive normalized chart-restriction coherence,
and split-torus Hom-fibre locality. It asserts no new external-source theorem.

`normalizedTransition` compares two actual split charts with the same direct
source. Its normalized pullback is the transition of their two normalized
restrictions. `overlapTransition` applies this to the actual scheme-theoretic
overlap of two charts, using the specified equal composite base map.

`locallyPermutes_of_residue_transition` assumes that each actual residue
transition is a coordinate permutation and produces an all-test permutation
on an open neighbourhood of that point. Hom-fibre locality extends that same
permutation as an equality of actual split-torus homomorphisms. Restriction
coherence identifies the further restricted overlap charts with the original
charts restricted to that open. Cancelling the source chart isomorphism gives
the coordinate square; the permutation's point formula proves `AgreeBy`.

For two `SuppliedBorelChart`s, restricting their actual quotient charts equals
the direct affine-model quotient chart at the composite map. On each overlap
residue field, the existing `basedComparison` derives a full based coordinate
comparison from the actual common supplied Borel, torus and ambient group.
Its `quotientChartOver_field_transition` proves that the actual quotient
transition is the induced simple-root permutation. The preceding locality
argument gives `quotientChart_locallyPermutes`, without assuming a based
comparison or a permutation atlas as an additional hypothesis.

`SuppliedBorelAtlas` chooses a chart and a point over every point of the original
base, using the proved supplied-Borel chart existence theorem. Its `cover` is
a small jointly surjective etale family. For any actual supplied full fppf
central quotient, `hasEtalePermutationAtlas` uses its actual quotient charts,
indexed by each chart's adapted simple-root support, and the proved local
permutation equations. The base is arbitrary, and the chart coordinate ranks
may vary. Empty simple-root supports are allowed. This pair constructs the
atlas; finite etale coefficient descent is provided separately.
