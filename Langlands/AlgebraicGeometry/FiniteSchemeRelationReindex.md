# Subfamilies of finite scheme presentations as actual charts

This is derived infrastructure for the finite family of symmetric tuple
charts used in Stacks Project, Lemma 68.8.6 (Tag 07ST), which refers to the
construction in Lemma 68.8.3 (Tag 0BBN). The registered originals are
`stacks-noetherian-approximation-2026-11-01` and
`stacks-stratification-2026-11-02`. The module proves a general fact about
finite scheme presentations, so it does not assume that the charts come
from tuples. It uses the coproduct and chart constructions already present
in the Library.

`schemeSigmaReindexMap X k` maps the coproduct of the selected schemes
`X (k j)` to the full coproduct. Its component equation is
`schemeSigmaReindexMap_ι`. The range criterion says that a point belongs
to its image exactly when it belongs to some selected component.
For an injective index map `k`, the selected component ranges are disjoint,
so this map is an open immersion. For finite families it is also a closed
immersion. The latter proof uses the finite coproduct criterion and the
injectivity of the open immersion.

For finite relation data `D`, `reindex k` selects the object charts
`D.U (k j)` and all cross relations `D.R (k j) (k l)`, with their existing
endpoint maps and laws on arbitrary scheme-valued points.
`reindexObjectMap` and `reindexRelationMap` are the induced coproduct maps.
The `first` and `second` equations state their endpoint compatibility.
The four immersion theorems apply the coproduct results to the object
indices and to ordered pairs of relation indices.

`mem_range_reindexRelationMap_iff` says that a relation point belongs to
the selected relation exactly when both of its endpoints belong to the
selected objects. To prove the reverse direction, decompose the relation
point into a component `(i,j)`. A selected component containing its first
endpoint identifies `i` with a selected index, and the second endpoint
identifies `j` with another selected index. The original relation point is
therefore in the corresponding selected pair component. This range
criterion does not require the index map to be injective.

For injective `k`, `reindex_isPullback_pair` proves the scheme-theoretic
pullback square of the joint endpoint maps along the product of the object
inclusions. Given compatible morphisms from any test scheme, the range
criterion places the morphism into the full relation in the image of the
open relation inclusion. The open immersion then gives a scheme
factorization. Monicity of the object inclusion identifies both endpoints,
and monicity of the relation inclusion gives uniqueness. This proves the
universal property on arbitrary test schemes, including disconnected and
nonreduced ones.

`reindexChartMap` is the explicit map from the selected relation scheme
to `Chart.arrows` of the full presentation along `reindexObjectMap`.
Its three equations retain the first endpoint, second endpoint and
underlying full-relation map. `reindexChartIso` identifies the two relation
schemes using their proved pullback properties, and
`reindexChartIso_hom` identifies its forward morphism with that explicit
chart map.

The comparison uses both endpoints. A selected object family need not be
invariant, so this module does not assert that its inclusion is a cartesian
source morphism of equivalence relations. It provides the actual induced
chart relation needed to restrict finite tuple presentations. It does not
prove a Noetherian first level.
