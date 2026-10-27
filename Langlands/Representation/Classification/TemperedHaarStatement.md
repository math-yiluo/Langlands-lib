# Fixed-Haar tests for analytic temperedness

This is a derived interface for the Library's existing analytic predicates.
It introduces no new definition of temperedness and asserts no unitarity result.

`Langlands.GLTemperedFixedHaarStatement` says that, for every prime `p`, every
`F : PadicField.{uF} p`, its supplied topological data `T`, every rank `n`, and
every complex representation on a carrier in the independent universe `uV`,
`T.IsTempered` is equivalent to `IsTemperedModCenter` at any one supplied Haar
measure. The supplied measurable space may be any Borel realization of the
actual quotient of `GL_n(F)` by its full group center. The predicate
`T.IsTempered` itself uses the Library's canonical Borel realization.

`Langlands.GLLeviTemperedHaarExtensionStatement` says that, for any block shape
`B`, the same action on the actual product group `B.Levi F.Carrier` is tempered
for every Borel realization and every Haar measure of its full central
quotient if it is tempered for one such realization and measure. The topology
throughout is induced by `T`; the group, its full center, the carrier, and the
action do not change. There is no positivity restriction on the total rank,
irreducibility assumption, or invariant-form assumption.

`Langlands.GLTemperedHaarStatement` is the conjunction of these two interfaces.
All field and carrier universes remain independent.

The provenance is internal and derived from the precise Library definitions
in `Classification.Tempered` and `RelativeRegularComparisonStatement`.
`Langlands.haarMemLpInvariant` supplies invariance of every coefficient's
`MemLp` condition under a change of Haar normalization, and
`Langlands.glBlockCentralQuotientTopology` supplies the required topology on
the actual GL and Levi central quotients. Two Borel realizations of a fixed
topological space have equal measurable spaces. These are the proposed
ingredients for a proof; the proposition declarations in this module do not
themselves prove the interfaces.
