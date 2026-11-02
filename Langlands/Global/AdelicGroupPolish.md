# Polish topology on actual finite-type adelic group points

Let `F` be a number field and `G` an affine group scheme locally of finite
type over `Spec F`. This internal derived construction equips the existing
finite adelic, archimedean and full adelic point spaces with second-countability
and Polish-space instances, and chooses a complete metric for the actual
norm-one subgroup. All topology statements refer to the existing
global-function evaluation topology and its subgroup and quotient topologies.

The coefficient rings are second countable by `AdelesSecondCountable`.
`affinePointsSecondCountableTopology` transfers this property along the
existing finite-coordinate embedding, separately for each coefficient ring.
The previously established local compactness, Hausdorffness and continuous
group operations then show each of these actual point groups is Polish.

The implemented generic argument uses the left uniformity of a topological
group. Its entourages are obtained by pulling back neighborhoods of the
identity, so first countability makes this uniformity countably generated.
Local compactness makes it complete by Mathlib's
`IsLeftUniformGroup.completeSpace_of_weaklyLocallyCompactSpace`. A complete
countably generated separated uniformity admits a compatible complete metric.
Together with second countability this is Polishness.

The norm-one subgroup is the existing intersection of all actual algebraic
character-norm kernels. Its established closedness gives Polishness as a closed
subspace of the full adelic points. `normOneCompleteMetricSpace` chooses a
compatible complete metric via Mathlib's `completelyMetrizableMetric`.
The two accompanying theorems identify its topology with the original subtype
topology and supply completeness. No particular distance formula or invariant
metric is asserted.

Both full and norm-one rational homogeneous quotients are second countable
because their actual quotient projections are open quotient maps. This file
does not assert Polishness of those homogeneous quotients, choose their
measures, prove unimodularity or finite volume, or provide reduction theory or
the split-centre quotient comparison.
