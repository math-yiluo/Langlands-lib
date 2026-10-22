# Compatible quotient-measure existence for closed subgroups

Worker 112 states `CompatibleMeasureExistsForClosedSubgroups`, the universal
existence theorem for the unchanged `CompatibleMeasureExists` predicate.
This file states a proposition and supplies no proof of it.

For every locally compact Hausdorff topological group `G`, every closed
subgroup `H`, and supplied regular Haar measures `μG` and `μH` that are also
right invariant, the proposition asserts `CompatibleMeasureExists H μG μH`.
The ambient group, subgroup and quotient have supplied Borel measurable
structures. The subgroup carries its subtype topology, and `LeftQuotient H`
its existing quotient topology. `IsHaarMeasure` includes nonzeroness,
positivity on nonempty open sets, finiteness on compact sets and left invariance
in the present topological group setting.

The conclusion expands to the existence of an actual nonzero regular measure
on `LeftQuotient H`, invariant under the existing right translations, with
integrability of the existing complex quotient averages of every continuous
compactly supported function and the exact Weil integral formula for the
supplied measures. No quotient measure or positive quotient functional is an
input. There is no countability hypothesis, and no Hausdorff or local compactness
hypothesis on the quotient beyond what can be deduced from the group and
closed subgroup.

This is an internal packaging of the mathematical theorem: all its hypotheses
are inside one universally quantified `Prop` definition. The original
`CompatibleMeasureExists` is a predicate on individual measures with fewer
assumptions; it remains unchanged, as do its imported definitions. Packaging
the full hypotheses makes the intended universal theorem available as a
separate exact proof target.

The mathematical provenance is the two-sided Haar specialization of Gerald
B. Folland, *A Course in Abstract Harmonic Analysis*, second edition (2015),
section 2.6, Theorem 2.51 and formula (2.52), printed pages 62–63 / PDF pages
75–76. Registered source: `folland-2015-abstract-harmonic-analysis-second`,
SHA256 `c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The original pages were read. Folland uses cosets `gH` with left translation;
the existing project convention uses `H*g` with right translation and averages
`f(h*g)`. Accordingly subgroup right invariance ensures descent. Requiring
both measures to be two-sided is the stated specialization of the source's
modular compatibility condition. This proposition asserts existence only;
it does not include the source's uniqueness conclusion.
