# Open subspaces and finite local chart covers in saturated atlases

These are internal consequences of domain saturation, the original atlas net
axioms, and the actual rational-neighborhood construction. The field, space
and atlas-index universes are independent. No global Hausdorff assumption
is imposed.

`exists_subchart_nhdsWithin_open` refines an original chart through a point
of an ambient open set to an original subchart lying in that set. Its range
is a neighborhood relative to the original chart range. The proof applies
`exists_subchart_neighborhood` in spectrum coordinates and uses the original
chart embedding to transport the neighborhood.

`HasAllLocalDomains.isOriginalChartDomain_of_isOpen` constructs the quasinet of original chart ranges
contained in an open subset. At a point the ambient atlas supplies a finite
family of chart neighborhoods. Refine each of those charts once using the
previous result. The finite-union formula for relative neighborhood filters
shows that the new union is still an ambient neighborhood. Pulling it to
the open subspace gives exactly the required quasinet. Thus the existing
`subspaceAtlas` construction applies to any open subset under the stated
domain-saturation assumption; this theorem does not supply that assumption
for an arbitrary atlas.

`openSubspaceAtlas` applies that proved condition to construct the actual
atlas on the induced open subspace. Its indices are exactly the original
charts contained in the open subset. Its algebras, spectrum charts and
bounded restrictions are inherited through `subspaceAtlas`, with no change
to the field, space or index universes.

`exists_finite_charts_cover_inter_open` combines this open-subspace quasinet
with the net's two-chart-intersection quasinet. The existing compact-subcover
theorem then gives finitely many original charts contained in both original
charts and the open subset, covering any specified compact subset of that
intersection.

`isCompact_inter_of_subset_t2Space` assumes that two original chart ranges
lie in one Hausdorff subspace. Both ranges are compact in that subspace, so
their intersection is compact there and hence in the ambient space.
`exists_finite_charts_inter_of_subset_t2Space` applies the original net's
compact-subcover theorem to this compact intersection. These last two
results do not require saturation or openness of the containing Hausdorff
subspace.

These are local topology and finite covering helpers. They do not construct
the analytic pullback presentation or prove the localized categorical or
etale conclusions of `LocalizedEtalePullbackStatement`. No external statement is transcribed.

The open-domain theorem is reused from `InvariantAnalyticDomains`; this module keeps the chart refinements, finite-cover results and `openSubspaceAtlas` construction.
