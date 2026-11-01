# Reconstruction from full strong maps on actual source chart domains

Author: Worker 36.

This derived construction works over a complete ultrametric normed field with
two supplied actual indexed affinoid atlas presentations `A` and `B`. The
coefficient, point and original chart-index universes `u`, `v` and `w` remain
independent. Chart algebras are the original presented positive-polyradius
affinoid algebras, and every algebra map below is bounded. Reducedness is not
assumed.

The original conventions are in Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), section 1.1, printed pp.13–14 /
PDF pp.10–11 (induced subset topology, quasinet and net), Definition 1.2.3
and Remark 1.2.4(i), printed p.16 / PDF p.13 (affinoid atlas and compatible
bounded restrictions), and Definition 1.2.7, printed p.18 / PDF p.15
(continuous maps with compatible affinoid maps for every admissible pair).
Registered source: `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These pages were reread for this unit. The reconstruction below is derived
from those conventions and the published actual chart-domain restriction
and topological colimit. It is not a separately numbered source assertion.

`StrongChartMapData A B` takes one full `StrongHom (A.chartPresentation i) B`
for every original source index `i`. Each source presentation is the actual
range subspace of chart `i`, with all original charts contained in it and
their original algebras and bounded restrictions. `baseMap_comm` requires
that local continuous maps agree after every original chart inclusion.
For `i` contained in `i'`, `pullback_comm` requires equality of the bounded
pullback at the whole chart `i` in its own source presentation with the
pullback at the same original chart in the presentation of `i'`, at every
admissible target chart. Admissibility witnesses may be different. These
are compatibility conditions on supplied full local maps; no global map,
monotone target choice, directedness or greatest target chart is input.
`StrongChartMapData.ext` compares the full local-map family; all remaining
fields are propositions.

`chartRangeCocone` uses each local continuous map as a leg from the actual
source chart range to `B.space`. Its naturality is `baseMap_comm`.
`baseMap` is the continuous map obtained by the published
`A.atlas.chartRangeDiagramCoconeIsColimit.desc`; it is constructed, not
assumed. No universe lifts are needed because the actual range diagram
lies in the point universe. The colimit factorization equation gives
`baseMap_apply`, equality of the global and local values on every source
chart subspace. `admissible_iff` then identifies global admissibility of
an original chart `c.val` with its admissibility inside any containing
source presentation. Its proof expands both images, using this value
formula and the literal original chart maps.

`toStrongHom` constructs the global full strong map. A containing target
for original source chart `i` is supplied by `localMap i` at its whole
source chart. For every globally admissible pair `i,j`, the global bounded
pullback is precisely that local whole-chart pullback. `toStrongHom_pullback`
records this equality. The local chart square and `baseMap_apply` prove
the global chart square. For source containment `i` in `i'` and target
containment `j` in `j'`, use the two-variable restriction equation of
`localMap i'`, from its subchart representing original `i` to its whole
source chart. `pullback_comm` identifies the smaller source pullback with
the one selected globally at `i,j`. The source restrictions are the original
bounded restrictions, so this gives the required equality of bounded
algebra homomorphisms.

`StrongHom.ext_of_pullback` supplies extensionality using equality of
continuous maps and equality of every bounded pullback with separate
admissibility witnesses. Its proof unpacks the two strong maps, substitutes
the continuous-map equality and applies the published `StrongHom.ext`.
`StrongHom.toStrongChartMapData` restricts a global strong map to each
original source chart. Both compatibility conditions are literal equalities
of the original continuous map and bounded pullbacks.

`toStrongHom_restrictSource` recovers each supplied local strong map in full.
The continuous maps agree by `baseMap_apply`. For a source subchart `c` of
`i`, the reconstructed pullback comes from `localMap c.val` at its whole
source chart. `pullback_comm` for `c.val` contained in `i` identifies it
with the supplied pullback of `localMap i` at `c`, at every admissible
target chart. Thus recovery includes all bounded maps, not just the maps
of spectrum points. `toStrongHom_unique` uses the published source-restriction
extensionality to prove uniqueness of the global map with these restrictions.
`toStrongHom_toStrongChartMapData` gives recovery of the whole compatible
local-data record. Conversely, `StrongHom.toStrongChartMapData_toStrongHom`
uses the same extensionality and local recovery to recover any original
global strong map. `strongHomEquiv` packages the two constructions and both
recovery laws as an equivalence.

The result concerns full strong maps on supplied original atlases and their
actual chart domains. It requires complete strong maps on each source
chart domain, rather than producing missing local bounded maps from point
maps. Atlas saturation and extension, finite affinoid algebra gluing,
unrestricted strong composition and localization, structure sheaves,
étale and equivariant sites, and the Harris tower remain separate
construction obligations.
