# Torus and cocharacter laws for actual pinned-model comparisons

This internal derived module packages the exact torus-square and positive-coroot
cocharacter clauses of `RelativePinnedComparison` as `PreservesTorus` and
`PreservesCocharacter`. Neither predicate asserts that the comparison preserves
pinning vectors or that it is a canonical normalization.

The inclusion and cocharacter pullback identities use the existing split-torus
composition identity and `Dynamic.baseChangeCocharacter_tower`. They include the
actual direct/iterated comparison `baseChangeCompIso`; no pullbacks are treated
as definitionally equal. Closedness of the original torus gives monicity of
`inclusionOver`.

Both clauses hold for identity comparisons, compose, and persist under
`AffinePinnedModel.pullComparison` along every scheme morphism. Conversely,
both are detected by one flat surjective cover locally of finite presentation.
The cocharacter reflection proof cancels the actual Gm and group pullback
identifications and applies fppf locality of equality of group homomorphisms.
For torus reflection the local torus isomorphism is conjugated by the actual
split-torus pullback identifications; the supplied local subgroup square then
descends uniquely by monicity. This does not select a constant root-lattice map.

The base and all test schemes are arbitrary. There are no connectedness,
nonemptiness, affineness or quasi-compactness hypotheses on them. These laws
support a future pinning normalization construction; they do not construct it
or prove `RelativePinnedComparisonExistenceStatement`.
