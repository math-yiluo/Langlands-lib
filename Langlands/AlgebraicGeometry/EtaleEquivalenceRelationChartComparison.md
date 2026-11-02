# Cartesian comparison of chart relations

Author: Worker 706.

This internal helper constructs morphisms between the chart relations defined
in `EtaleEquivalenceRelationChart`. Its mathematics is derived from the
published scheme-valued equivalence relation axioms and the universal
properties of fibre products. The source-square convention for cartesian
relation morphisms is Stacks Project Definition 39.21.1, Tag 0APD,
registered as `stacks-etale-equivalence-relations-2026-11-01`.
The motivation is restriction to charts in the stratification and
Noetherian approximation arguments of Tags 0BBN and 07ST, registered as
`stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. This helper assumes no
approximation or quotient existence statement.

All declarations lie in `EtaleEquivalenceRelation.Chart`. Suppose that
`f : E.U → F.U` and `g : E.R → F.R` commute with both endpoints, that
`a : V → E.U` and `b : W → F.U` are chart maps, and that
`k : V → W` satisfies `a ≫ f = k ≫ b`.
Then `hom` sends an arrow with lifted endpoints in `V` to its image
under `g`, with both endpoints mapped under `k`. It is constructed by
`Chart.lift`; `hom_t`, `hom_s`, and `hom_map` recover these three
components. Neither chart map needs to be étale for this construction.

`isPullback_hom_s` assumes that `(f,g)` is cartesian and that the square
with projections `a` and `k` and bottom maps `f` and `b` is a pullback.
It proves that the induced map on chart arrows and `k` form a pullback
square for the chart source maps. The proof gives the universal property
explicitly. Uniqueness first recovers the underlying arrow using the
original source pullback square, then recovers the other chart endpoint
using the chart object pullback. Existence first lifts the original arrow
with its prescribed source; the chart object pullback then lifts its other
endpoint. The three components give the required chart arrow.

`isCartesianHom` packages this source pullback and the equation `hom_t`
as a cartesian morphism between `E.chart a` and `F.chart b` when both
chart maps are étale. All schemes and constructions retain the arbitrary
universe `u`.
