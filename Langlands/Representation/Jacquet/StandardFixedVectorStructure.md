# Local structural inputs for the standard fixed-vector argument

Worker 1649. This is internal adapter infrastructure for the exact published
VI.9.4 fixed-vector statements. It derives closedness of their actual standard
Levi and unipotent point subgroups, compact-open containment in the latter,
and connected reductivity of the canonical standard Levi from hypotheses
already present in those statements.

The closedness proofs apply
`Langlands.AlgebraicGeometry.PointTopology.isClosed_rationalPoint_subgroup`
to the closed representatives in
`Langlands.GroupScheme.Standard`. They use only an affine ambient group over
a Hausdorff topological field. In particular, neither closedness proof needs
a standard cocharacter, a maximal split torus or a root-system comparison.
The topology is exactly `rationalPointTopology F G.X`, and each subgroup
has its inherited topology.

The general `compactOpenContainment_of_closed_subgroup` lemma takes subgroups
`N ≤ U` of a topological group carrier, with `N` closed in the ambient
space. Given a compact subset of `N`, it maps that subset into `U`, chooses
a compact open subgroup there, and pulls that subgroup back along the
inclusion. The pullback is open by continuity. It is compact because it is
the inverse image under the closed embedding of `N` into the ambient space
of the compact ambient image of the chosen subgroup.

For the actual standard unipotent group over a nonarchimedean local field,
one local witness `∃ zeta, IsStandardCocharacter i ν J zeta` includes that
group in the dynamic unipotent group of `zeta`. The published theorem
`Langlands.BruhatTits.dynamicUnipotentCompactOpenContainment` supplies
compact-open containment for that larger group. Closedness and the general
pullback lemma then supply it for the standard group. Forgetting openness
gives `Localization.IsLimitOfCompactSubgroups`; specializing a compact
subset to a finite set gives the finite-subset condition of smooth
coinvariant exactness. Only inclusion in the dynamic group is used, so no
equality of standard and dynamic subgroups is assumed or proved.

The definition `standardUnipotentCompactOpenSubgroup` chooses one such open
subgroup for each compact subset of the actual standard unipotent group.
Its specification theorem proves that the chosen subgroup is compact and
contains that subset. The choice has no uniqueness or compatibility claim.

Finally, the imported
`IsCompatibleStandardSplitComponent.standardLeviScheme_isConnectedReductive`
from `RationalHoweJointAssemblyProof` supplies the reductive-Levi implication.
`IsCompatibleStandardSplitComponent` includes a connected
reductive group scheme representing the same all-test standard Levi
functor as `Standard.leviScheme`. The published
`SubgroupFunctor.IsRepresentedBy.isConnectedReductive` theorem transports
connected reductivity between the two representatives. This uses the
compatible component already supplied for each index by the exact
VI.9.4 hypothesis; it does not establish the general structural
standard-cocharacter or Levi-intersection statements.

All results are derived from the named published constructions and proofs.
No new literature assertion is claimed. These adapters do not prove either
unconditional VI.9.4 statement, supply the generalized Jacquet lemma, or
discharge the remaining root-system, standard-subgroup comparison,
Levi-intersection or rational cuspidal-restriction prerequisites.
