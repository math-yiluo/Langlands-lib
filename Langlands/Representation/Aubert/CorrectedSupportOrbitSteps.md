# Actual orbit differences for corrected support steps

This internal bridge proves that the active singleton steps of the corrected
Weyl filtration have the required actual single-orbit geometry.

Distinct inverse-permutation Borel cells are disjoint, by the published
injectivity of their actual double-coset classes. Consequently
`bruhatSupport_sdiff` proves that passage from Weyl subsets to actual matrix
Bruhat unions preserves set difference. The published two directions of the
Weyl-to-parabolic double-coset comparison then identify the Bruhat union of a
block Weyl double coset with exactly the corresponding actual parabolic matrix
double coset, retaining the inverse-permutation convention.

If `w` belongs to the corrected core of `θ`, the published Weyl singleton-step
identity says that removing `w` from `θ` removes precisely the entire Weyl
double coset of `w` from the core. `corrected_bruhatSupport_singleton_step`
transports this identity to actual matrices.
`correctedQuotientSupport_singleton_step` transports it further to the actual
inducing left quotient, using the exact support preimage identities and the
actual coset-orbit membership criterion. The difference is exactly the orbit
of the coset of the inverse permutation matrix.

For any supplied p-adic topology, `correctedOpenOrbitSupportPair` bundles these
actual subsets as an `OpenOrbitSupportPair`. Its hypotheses specify that both
`θ` and `θ` with `w` removed are length-compatible upper tails and that `w`
belongs to the corrected core. Their openness follows from the proved compact
representative and Bruhat boundary topology result. Right-parabolic invariance,
containment and the single-orbit difference are proved, rather than supplied
as representation-theoretic hypotheses. Rank zero is included.

The provenance is internal, from the published actual matrix double-coset
comparison and corrected Weyl singleton identities, together with the actual
support topology construction. This module supplies concrete geometry for
orbit restriction; it does not identify Jacquet coefficients or cross-cut maps,
prove exterior-sign compatibility, or assert concentration or effectivity.
