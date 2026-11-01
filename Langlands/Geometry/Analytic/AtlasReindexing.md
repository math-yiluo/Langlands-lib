# Transport of actual atlases along index equivalences

Author: Worker 36.

This is internal infrastructure for comparing constructed atlas presentations
whose chart indices initially occupy different universes. It imports the
published actual atlas, strong-map and strong quasi-isomorphism constructions.
It adds no analytic existence hypothesis and uses no new literature assertion.

For a complete ultrametric normed field `K : Type u`, a topological space
`X : Type v`, an actual atlas `a : IndexedAffinoidAtlas.{u,v,w} K X`,
and an equivalence `e : J ≃ a.Index` with `J : Type z`, `a.reindex e`
constructs an atlas with index universe `z`. The field and point universes
remain `u` and `v`; `w` and `z` are independent.

The algebra and chart at `j` are literally the original algebra and chart at
`e j`. Every bounded restriction is the entire original restriction at the
corresponding pair. The three `reindex_algebra`, `reindex_chart` and
`reindex_restriction` equations are definitional equalities.
`reindexed_chartFamily` proves equality of the chart families using the
surjectivity of `e`. This transfers the original net condition. Injectivity of
`e` and the original chart-domain injectivity establish injectivity for the
reindexed atlas. Local Hausdorffness, chart embeddings, full factorization
against every presented affinoid test, and bounded identity and composition
equations are the original proved fields at the corresponding indices.

`AffinoidAtlasPresentation.reindex` bundles this atlas on the original
topological space. `reindex_space` is a definitional equality; neither points
nor their topology are lifted or replaced.

For a full strong map `f : StrongHom A B` and equivalences `eA` and `eB`
from types in a common new index universe to the original indices,
`f.reindex eA eB` constructs the full strong map between the reindexed
presentations. Its continuous map is literally `f.baseMap`. A target supplied
by `f.target_exists` is transported with `eB.symm`. Every admissible pullback
is exactly `f.pullback (eA i) (eB j) h`. The chart squares and simultaneous
source and target restriction compatibility are the original equalities of
complete bounded maps. The three equations `reindex_baseMap`,
`reindex_pullback` and `reindex_chartImageLocus` expose these facts.

`StrongHom.IsQuasiIso.reindex` retains the original ambient homeomorphism and
each full affinoid-domain representation. Conversely, applying the reindexed
representation at inverse indices recovers the original one. This proves
`isQuasiIso_reindex_iff`, including the universal property on all the original
positive-polyradius presented affinoid test algebras.

The provenance is solely transport of published constructions along a supplied
equivalence. This is useful, for example, when a singleton atlas indexed by
`PUnit.{1}` must be compared in the same `StrongHom` type with an atlas indexed
in universe `u`. It does not equate different index universes, identify
different quotient presentations, or infer equality of algebra maps from
their point maps. Empty spectra and nonreduced algebras are retained. No
general atlas extension, saturation, analytic gluing, unrestricted strong-map
composition, localization, structure sheaf or étale site is constructed here.
