# Unimodularity targets for actual adelic Haar measures

This module states the two assertions of Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), §3.6, Lemma 3.6.4, printed p.90, at
the connected number-field scope of the host construction.

`NormOneHaarRightInvariantStatement` asks that, for every number field F
and every smooth connected affine F-group G whose structure morphism is
locally of finite type, the existing Haar measure on the actual subgroup
G(A_F)^1 be right invariant. The subgroup is the existing
`normOneSubgroup F G`, the intersection of the kernels of the normalized
idelic norms of all actual F-rational algebraic characters of G. The
measure is `Measure.haar` on this subgroup with its existing topology
and measurable structure. It is not the restriction of full ambient
Haar measure. Reductivity is not a hypothesis of this first target.

`ConnectedReductiveHaarRightInvariantStatement` asks that the existing
`Measure.haar` on the full actual point group `AdelicGroupPoints F G`
be right invariant whenever G satisfies the existing
`Langlands.GroupScheme.IsConnectedReductive` predicate. That predicate
asserts smoothness, affineness, connectedness and trivial geometric
unipotent radical. The explicit affine and locally finite type
hypotheses provide the existing locally compact point-group and Haar
interfaces. Neither target requires a split group, an isotropic group,
or F to be the rational field.

Both conclusions are the precise property
`Measure.IsMulRightInvariant` of the fixed Haar measures used by
`AdelicGroupHaarMeasure`. Since those measures are already left Haar
measures, this property expresses unimodularity. In particular it asks
for invariance under every positive right translation x ↦ xg, matching
the convention of the existing rational quotient measure API.
`AdelicHaarUnimodularityStatement` is the conjunction of the two
targets. All three declarations are proposition definitions. They
install no right-invariance instance and assert no proof.

The section's standing hypothesis on printed p.87 is a smooth affine
algebraic group over a global field. Lemma 3.6.4 does not impose
connectedness on its first assertion, and the second only assumes that
the neutral component is reductive. These Lean targets deliberately
restrict both assertions to connected groups over number fields. The
smooth affine finite type condition agrees with the host scope:
affineness together with locally finite type over a field gives finite
type. The function-field and disconnected extensions are not included.

The source proves the first assertion using the adelic analytic
modular-character identity (3.12) and the actual rational determinant
character (3.13). For the second it uses the product of local modular
characters and Corollary 3.6.2. The preceding Proposition 3.6.1 derives
the local analytic modulus from invariant differential forms. None of
these comparisons is proved or assumed by the present proposition
definitions. A proof of the targets must establish the required
analytic invariance on the existing point groups; an algebraic
determinant character alone does not establish it. In passing from
ambient modular triviality to Haar measure on the norm-one subgroup,
the required subgroup modular comparison must also be justified.

These targets provide the missing hypotheses of the existing actual
rational quotient right-translation and complex Weil compatibility
theorems once proved. They do not assert finite volume, split-centre
decomposition, Siegel coverage, or identification of a particular local
product normalization with the fixed Haar measures.

The original §3.6, printed pp.87–90, was read, including the displayed
formulas and Lemma 3.6.4. The five-page October 2026 author errata was
checked and contains no correction to that lemma.

Source records: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
§3.6, printed pp.87–90, especially Proposition 3.6.1, Corollary 3.6.2,
equations (3.12)–(3.13), and Lemma 3.6.4;
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
October 2026, all five pages.
