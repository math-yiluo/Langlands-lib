# Actual rational-point rank-one assembly from support detection

Author: Worker 64.

This internal conditional construction specializes
[`rankOneJacquetConstituentsOfSupportDetection`](RankOneJacquetSupportDeduction.md)
to the actual rational points of every connected reductive group scheme over a
nonarchimedean local field. It retains independent universes `u` and `v`;
representation carriers have universe `max (u + 1) v`. The ambient topology is
literally `pointTopology`, the indices are finite sets of `SimpleRoot i ν`,
and the subgroup families are the actual `parabolic i ν`, `levi i ν` and
`unipotent i ν`. There is no restriction on characteristic or splitness.

`rankOneJacquetConstituentsOfRationalSupportDetection` assumes the published
`RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v}` and
instantiates it at the supplied field, connected reductive group, maximal split
torus, generic cocharacter and actual structural inputs. The finite simple-root
enumeration comes from `simpleRelativeRootFintype`. Both ambient and inside-Levi
semidirect decompositions are derived through the published
`isSemidirectDecomposition_of_standardCocharacterStatement` and
`isSemidirectDecomposition_in_levi` adapters. Closedness of the radicals and
Levis, local compactness, the nonarchimedean group structure and Hausdorffness
remain explicit premises.

The generic assembly's identity association and associate-properness premises
are proved here. `rootAssociation_one` supplies the literal identity
representative at `J`. For every actual association from `J` to `K`,
`rootAssociation_ne_univ` transports the supplied properness `J ≠ univ` to
`K ≠ univ`. These laws concern the actual root action and literal simple-root
labels. There is no replacement association relation. The supplied
`IsCorollaryLeviCuspidal` hypothesis is converted to `IsLeviCuspidal` by
`isCorollaryLeviCuspidal_iff_isLeviCuspidal`, which only changes the equivalent
descriptions of a zero actual smooth object.

The compact-limit property of every actual unipotent radical is derived by
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
from `RationalUnipotentRegularity`, applied to the same `hStandard`, `hG`,
`hi` and `hν`. Its proof identifies the actual standard unipotent subgroup
with a dynamic unipotent subgroup and uses the published dynamic compact
containment theorem. Thus no compact-limit or exactness premise is added.

The other inputs are an irreducible cuspidal `σ`, two actual finite-length constituents
`A`, `B` with `HasTwoConstituents`, a normalizer point `n` and its actual
self-normalization witness `hself`, an actual geometric middle short exact
sequence at `J`, and zero middle Jacquet modules at every other proper subset.
The published generic deduction uses support-category membership, closure under
actual subquotients and exactness of actual normalized Jacquet restriction to
prove that both endpoint Jacquet modules at `J` are nonzero. Its assembly then
orders the two constituents and gives the actual `RankOneJacquetPattern`.

The returned subtype contains an ordered pair of actual finite-length objects,
their actual constituent sequence, object isomorphisms `r_J ρplus ≅ σ` and
`r_J ρminus ≅ Ad(n⁻¹) σ`, and zero-object assertions at every other proper
subset. The input `n` and `hself` occur literally in the conclusion. The
inverse-conjugation pullback acts by `x ↦ σ(n*x*n⁻¹)`. The construction works for
any supplied self-normalizing lift and so can be applied to each specified
longest lift when its remaining inputs are proved. It does not assume that the
two irreducible factors are distinct or that either short exact sequence
splits.

This is a deduction from the named published declarations, with no new external
source claim. Its transitive representation-theoretic dependencies are described
in [the generic support deduction](RankOneJacquetSupportDeduction.md) and
[the exact-data assembly](RankOneJacquetAssembly.md): elementary actual
subquotient conversions, support-category closure and induction membership,
`jacquet_subsingleton_of_isSubquotient`,
`jacquetFunctor_map_isShortExact`, `characterLocalizationExactness`, actual
irreducibility transport and two-simple-endpoint matching. The present module
adds the actual-family adapters, the elementary root-association laws and
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
The latter uses `BruhatTits.dynamicUnipotentCompactOpenContainment` through
`BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups`, as documented in
[the actual unipotent regularity adapter](RationalUnipotentRegularity.md).
It invokes no proved instance of a cuspidal-support theorem, classification,
character independence, adjointness or geometric lemma.

The support detector, constituent existence,
geometric sequence and other-proper middle vanishings remain supplied
obligations. An empty simple-root type admits no proper `J`, consistently with
the maximal-standard condition in the host target; no nonemptiness instance is
added. This construction does not prove
`RationalRankOneJacquetModulesStatement`, and its additional premises do not
change that exact target or count as its proof.
