# Reconstructing chosen atlas maps from bounded chart pullbacks

Author: Worker 36.

For two supplied `AffinoidAtlasPresentation` objects, `ChartMapData A B`
contains a monotone choice of target chart for each source chart and actual
bounded algebra pullbacks satisfying the bounded restriction squares. It does
not take an ambient map as input. The coefficient, space and index universes
`u`, `v` and `w` remain independent.

`ChartMapData.chartFunctor` is the functor between actual chart-containment
orders induced by the target choices. `chartAffinoidMap` packages the supplied
bounded pullbacks in the opposite category of presented affinoid algebras.
Its naturality is exactly the input equality of bounded restriction composites.
`chartSpectrumMap` applies the genuine spectrum functor. After explicit
universe lifting, composing this transformation with the target atlas's
chart cocone gives `chartCocone` on the source spectrum diagram. Its vertex
is the lifted original target space, and its legs are the actual spectrum maps
followed by the selected target chart embeddings.

`liftedBaseMap` uses the published source spectrum-chart colimit to construct
the continuous map between lifted original spaces. `baseMap` removes the lifts
using continuous `ULift.up` and `ULift.down`. `chart_comm` is the chart evaluation
formula of that colimit with `ULift.down` applied. `baseMap_unique` lifts any
competing continuous map with the same chart formulas, uses the colimit's
extensionality on chart points, then removes the lifts.

`toHom` constructs the existing chosen atlas arrow from this ambient map and
the original chart choices and bounded pullbacks. The formulas
`toHom_indexMap` and `toHom_pullback` are definitional equalities.
`Hom.toChartMapData` forgets an existing arrow's ambient map and chart formula.
Its reconstructed ambient map is the original one by `baseMap_unique`.
`Hom.toChartMapData_toHom` then uses arrow extensionality, retaining the exact
dependent bounded-map family. Conversely `toHom_toChartMapData` is reflexive.
These laws give `ChartMapData.homEquiv`, an equivalence with the existing
chosen atlas morphism type. Equality of ambient functions alone is not used
to identify bounded pullbacks.

This is derived infrastructure for the chosen-map specialization. Berkovich,
*Etale cohomology for non-Archimedean analytic spaces* (1993), Definition 1.2.3
and Remark 1.2.4(i), printed p.16/PDF p.13, give actual affinoid atlas charts
and bounded restriction composition. Definition 1.2.7, printed p.18/PDF p.15,
requires a continuous map and compatible affinoid maps for every admissible
chart pair. The construction here derives the continuous map for the additional
monotone chosen-target data of the published `Hom`; it does not identify those
data with all strong morphisms. Its topological gluing uses the published
spectrum colimit, itself derived from the source's net topology in section 1.1
and Lemma 1.1.1(i), printed pp.13-14/PDF pp.10-11. The original source is
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Original PDF pp.13-15 were reread for this unit. This categorical reconstruction
is a consequence of the already implemented atlas and colimit data, rather
than a theorem attributed verbatim to the source.

The supplied atlas objects and their actual algebras remain input. General
all-admissible strong-morphism composition, extended atlases, refinement
localization, section-algebra gluing, structure sheaves, and analytic sites
remain separate construction obligations.
