# Original chart colimits with full bounded strong maps

The original chart-domain presentations of a supplied directed affinoid atlas
have that presentation as their colimit in `DirectedAtlasPresentation`.
The arrows and the universal map retain every admissible bounded algebra
pullback. Forgetting to the underlying topological spaces preserves this
particular colimit.

The coefficient field `K : Type u` is complete, normed and nonarchimedean,
expressed by `NormedField K`, `IsUltrametricDist K` and `CompleteSpace K`.
Ambient spaces have universe `v` and chart indices have universe `w`,
independently of `u`. The category uses the published full `StrongHom` arrows
and their directed composition. The affinoid algebras are the published
presented affinoids; reducedness is not assumed.

`AffinoidAtlasPresentation.directedChartDiagram` is defined for any supplied
presentation. It takes the order of its original chart ranges to their actual
chart-domain presentations, with all contained original charts and the original
bounded restrictions. Each chart-domain presentation has its whole original
chart as a top chart, so it determines a directed object even when the ambient
atlas is not directed. This diagram is the published `chartStrongDiagram`
followed by `topChartFunctor`. Its composite with `spaceFunctor` is
definitionally the original `chartRangeDiagram`.

For `A : DirectedAtlasPresentation K`, `chartCocone` has vertex `A` and the full
chart inclusions as legs. Each inclusion is source restriction of the identity;
it retains the entire target atlas. The nested-source composition law proves
cocone naturality. `chartCocone_spaceFunctor` identifies its image exactly with
the original range-inclusion cocone.

For any cocone `s` on this diagram, `chartDescBaseMap` constructs a continuous
map from `A` to `s.pt` using the published topological colimit of the chart
ranges. `chartDescBaseMap_chart` proves agreement with each continuous leg
on the whole chart range. The two admissibility equivalences transport image
containment between the ambient atlas and a cocone leg, first at its top chart
and then at every original chart contained in its domain.

For each original source chart `i` and every target chart `j` containing its
descended image, `chartDescPullback` takes the bounded map directly from the
leg at `i`, evaluated at that domain's whole chart. Thus it constructs all
admissible pullbacks without selecting a target-index function.
`chartDescPullback_naturality` proves the full two-variable restriction
equation. For a source inclusion `i ⊆ i'`, cocone naturality identifies the
leg at `i` with that inclusion followed by the leg at `i'`. Evaluating the
published directed-composition formula on the two top charts gives the source
restriction equation; the leg's target restriction equation then gives the
required simultaneous source and target naturality. Equality is equality of
bounded algebra homomorphisms themselves.

`chartDesc` combines these maps into a full strong morphism. Target existence
comes from each leg at its top chart, the spectrum square comes from that
leg's square and continuous agreement, and bounded naturality is the preceding
equation.

`chartDesc_restrictSource` proves equality with every entire cocone leg,
including its pullbacks on all contained original charts. Continuous agreement
is already known. For a contained chart `c ⊆ i`, cocone naturality compares
the legs at `c` and `i`. Evaluate the bounded composition through the chart
`c` inside the domain `i`. The inclusion's pullback is then the original
restriction from `c` to itself, which is the bounded identity. This recovers
the leg at `i` on that contained chart. Directed algebraic extensionality
recovers all admissible target pullbacks. The proof uses the bounded data
and does not infer equality of algebra maps from their spectrum-point maps.

`chartCocone_fac` rewrites composition with a full source inclusion as source
restriction, then applies leg recovery. `chartCoconeIsColimit` uses
`chartDesc` for its descent map and this factorization law. Uniqueness follows
from the published locality theorem `StrongHom.ext_of_restrictSource`:
the factorization equations determine every full source-chart restriction.
`spaceFunctorPreservesChartColimit` follows from this colimit and the
published topological range colimit, since forgetting the cocone gives that
same range cocone.

This is derived infrastructure from Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`:
section 1.1 and Lemma 1.1.1(i), printed pp.13–14 / PDF pp.10–11,
give the topology determined by a quasinet; Definition 1.2.3 and
Remark 1.2.4(i), printed p.16 / PDF p.13, give the atlas and transitive
bounded restrictions; Definition 1.2.7, printed p.18 / PDF p.15,
requires compatible morphisms for every admissible chart pair. The categorical
colimit, full bounded descent and preservation statement here are derived
consequences of these conventions and the published actual chart-domain and
topological-colimit constructions. They are not separately numbered claims
from the source.

The ambient source and every cocone vertex are directed because they are
objects of the existing directed category. This additional hypothesis belongs
to this formal construction. It does not establish unrestricted strong
composition, extension to a larger atlas, gluing of an arbitrary diagram of
affinoids, localization by refinement, or an analytic or equivariant site.
