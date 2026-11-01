# Enlarging strict atlases of actual line bundles

This is a derived geometric construction from `LineBundleStrictAtlas`,
`CommonSourceTransitionTransport`, `OpenPairLineBundleGluing`, and
`StrictCocycleAtlas`. It adds no literature assertion or algebraic extension
hypothesis. All schemes and the chart index retain arbitrary universe `u`.

A `CommonSource` realizes the selected chart bundles by pullbacks of one actual
module on a scheme mapping monomorphically to the ambient scheme.
`CommonSource.changeSource` replaces that module by an identified pullback
from another monomorphic source. The old chart maps are composed with the
source change and their comparisons use `sourceComparison`.
`changeSource_transition` applies `transition_changeSource` and concludes
literal equality of each old ambient transition isomorphism.

`ChartData` keeps a single chart map, its ambient factorization and its actual
module comparison together. `insertData` retains this entire record for each
old index. For a new index it uses the supplied chart map and comparison.
`insertData_old` proves equality of the retained records; if the new index
was already present, the old record is retained as well. `insert` assembles
these records into a common source on the enlarged index set.
`insert_transition` applies congruence to both whole chart records, proving
literal equality of all old transitions without separately transporting the
dependent comparisons.

`CommonSource.enlarge` additionally assumes that the common source map is an
open immersion and that its module is locally free of rank one. Given one
actual overlap isomorphism with another chart bundle, `OpenUnion.glue`
constructs an actual line bundle on the union of the two open images.
`changeSource` uses its left comparison to retain all old chart data, and
`insert` uses its right comparison to add the new chart. The resulting common
source realizes every chart in the enlarged set. `enlarge_transition` combines
the preceding two preservation lemmas and retains every old transition exactly.

`maximal_contains_chart` applies this construction to the actual realization
of a maximal good atlas. Its module is the glued line bundle and its source
map is the inclusion of the covered open. The enlarged common source gives
triple witnesses for every triple, and exact transition recovery identifies
its old transitions with the original atlas labels. `maximal_domain` then
shows that inserting the new index does not change the domain. Hence any
chart supplied with the displayed overlap isomorphism is already present.

This is a prerequisite of general line-bundle extension. It assumes the
overlap identification as data. Producing such a compatible chart near an
uncovered point, establishing full coverage, and proving the unchanged
general extension statement remain further obligations.
