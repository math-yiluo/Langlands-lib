# Local rational heights on actual atlas refinements

This internal construction preserves the existing local kernel-rank height
condition when restricting an actual global rational atlas map to a finer
principal cover. The scalar ring is an arbitrary commutative ring. The
coefficient ring and rational scalar field share a universe; tests use that
coefficient universe. Source and target have finite, possibly different
coordinate types and the same specified original cover. Original and finer
covers may be infinite.

`HasConstantChartHeight.restrictCover` uses the actual cover refinement and its
retargeting to the target atlas. On each defined test chart,
`BasicAtlas.RationalHom.onChart_restrict` identifies the restricted rational
map with composition by the actual source and target chart isomorphisms.
`RationalSection.HasHeightFunction.ofGlobal_isoTransport` transports the
existing height presentations through the inverses of these same isomorphisms.
Both kernel-rank exponents, the scalar denominator exponent and their signed
difference remain unchanged. Thus the same integer is a height on every
test chart of the finer atlas.

`refinedLocalQuasiIsogeny` additionally takes nonvanishing of the distinguished
scalar in the rational field and actual scalar divisibility of the selected
original source and target laws on that test. The same chart isomorphisms
transport divisibility, and the preserved height condition supplies local
scalar-isogeny presentations. The result is a genuine `LocalQuasiIsogeny`,
whose section is exactly the canonical section of the restricted rational
atlas map. `refinedLocalQuasiIsogeny_height` proves the same constant height
for this section.

The provenance is internal: this combines the existing actual rational atlas
restriction, formal chart isomorphisms, kernel-rank height transport and
scalar-divisibility transport. It neither chooses numerical heights nor
asserts height uniqueness, additivity, coefficient-base-change invariance,
exhaustion of local rational maps, framed comparison classes or
representability. Full-order rational maps and quasi-isogenies use the same
underlying restriction, so their existing ambient height relation is covered
by this result as well.
