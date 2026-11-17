# Rigidity and uniqueness of pinned inner comparisons

`PinnedInnerRigidity` says that two actual comparisons of supplied affine pinned
models over any common scheme are equal if they are fppf-locally pinned and
fppf-inner-equivalent. The theorem `pinnedInnerRigidity` proves this condition in
every universe. There are no extra hypotheses on the coefficient rings or the
common scheme. This is an internal consequence of the actual pinning and
conjugation constructions, not an assertion of existence of a pinned comparison.

`mem_center_of_torus_representsIso` first proves full relative centre membership
for a torus point representing a self-comparison that preserves the local
pinning. For each refinement and each group point, it projects the required
commutation equation to the original affine group using
`baseChangePointsEquiv`. The relative group over the common scheme need not have
an affine total space. Maps into the original affine total space are detected
on local rings with separably closed residue fields. On each such test the
coefficient algebra structure is recovered from the actual spectrum map, and
`mem_center_coefficientTest_of_representsIso` supplies commutation. Its
multiplicative point equivalence then reflects the equation. This argument
retains arbitrary coefficient rings, including nilpotents.

`mem_center_of_representsIso` removes the torus premise: cocharacter
preservation puts every representing point in the actual torus by
`torusConjugator`. It then applies the preceding centre result. Both centre
conclusions use the unchanged full centre functor, which quantifies over every
relative refinement and every group point there.

`eq_refl_of_locallyPinned_locallyInner` takes an actual fppf cover and
conjugating point witnessing local innerness. That point is central by the
preceding result. On the pullback of this cover to each test scheme,
conjugation is therefore the identity. Epimorphism cancellation reflects this
identity to the original test. Applying this to the discrepancy of two
concretely pinned comparisons proves
`eq_of_locallyPinned_innerEquivalent`.

`eq_refl_of_fppfLocallyPinned_locallyInner` pulls back to the supplied fppf
pinning cover, applies concrete rigidity, and reflects equality with
`pullComparison_injective`. Applying it to the discrepancy proves
`eq_of_fppfLocallyPinned_innerEquivalent`, the asserted general uniqueness.
The inverse and composition laws for the actual pinning predicates ensure
that the discrepancy is pinned.

These are rigidity results only. Constructing corrected comparisons,
establishing their descent compatibility, and assembling the unchanged
`RelativePinnedComparisonExistenceStatement` remain separate obligations.
