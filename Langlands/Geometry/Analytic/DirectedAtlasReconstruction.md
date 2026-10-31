# Full strong morphisms from compatible bounded local choices

Author: Worker 36.

For supplied `AffinoidAtlasPresentation` objects `A` and `B` over a complete
ultrametric normed field `K`, this module constructs a full `StrongHom A B`
from independently chosen bounded local algebra maps. The coefficient, ambient
space and original chart-index universes `u`, `v` and `w` remain independent.
The original algebras are actual finite positive-polyradius presented affinoid
algebras, including their displayed closed quotient ideals. All pullbacks below
are bounded `K`-algebra homomorphisms. No reducedness hypothesis is imposed.

`LocalChartMapData A B` supplies a target index `indexMap i` for each original
source index `i`, a bounded map from that target algebra to the source algebra,
and the following compatibility. Whenever source chart `i` is contained in
source chart `i'`, there is one original target chart `q` containing both
selected target charts, such that the two resulting bounded maps from the
algebra of `q` to that of `i` agree. These are actual algebraic restriction
equalities. The ambient map and pullbacks at all other admissible pairs are
outputs of the construction. The selected target indices need not be monotone. Target
directedness is needed for the full strong morphism; the initial ambient-map
construction uses only the common upper charts already in the local data.
Neither source directedness, compactness of the ambient spaces, nor nonempty
chart-index types is assumed.

`pullbackToUpper` composes a selected bounded map with an actual target
restriction. `chartCocone` applies spectrum comap to each selected bounded map,
then the target chart embedding, with the explicit universe lifts of the
published source spectrum diagram. Its naturality follows by evaluating the
input bounded compatibility equation on a spectrum point in the supplied
common upper chart, then using the two target restriction squares. This
constructs a cocone directly; it requires no functor between chart orders.
`liftedBaseMap` descends that cocone through the published
`chartSpectrumCoconeIsColimit`. `baseMap` removes the lifts continuously.
`chart_comm` is precisely its evaluation on each original source chart, and
`image_chart_subset` gives containment in the selected target chart.
`baseMap_unique` uses the colimit's chartwise extensionality to identify any
continuous map with the same chart formulas.

For each `i`, `localHom` constructs an existing chosen atlas arrow from the
actual chart-domain presentation `A.chartPresentation i` to `B`. Its base map
is the inverse of the source chart homeomorphism followed by the selected
spectrum comap and target chart embedding. Every target choice is constant
at `indexMap i`, and its pullback on a source subchart is the original source
restriction composed with the selected bounded map. Source restriction
composition proves this arrow's compatibility. `localHom_pullback_top`
recovers the supplied bounded map. `localHom_baseMap` proves that its
continuous map is the restriction of the constructed `baseMap` along the
actual `chartInclusion`; `localHom_admissible` transfers each ambient
admissibility condition to this chart-domain arrow.

Assume `hd : B.atlas.HasDirectedCharts`, meaning that every two original target
chart ranges lie in a third original target chart range.
`fullPullback d hd i j h` applies the published `Hom.directedPullback` to the
top chart of `localHom d i`. That construction uses the full affinoid-domain
universal property, tested against every presented affinoid algebra over `K`,
to produce the bounded map from the algebra of any admissible target chart
`j` to the algebra of `i`. `fullPullback_comp_restriction` gives its exact
bounded factorization through every common upper chart. `fullPullback_chart`
proves its spectrum square with the constructed ambient map.

`pullbackToUpper_comp` follows from target restriction composition.
`restriction_comm_upper` upgrades the input equation, which holds in one
upper chart, to the same equation in every common upper chart: place that
chart and the input witness in a further original chart, compare the bounded
composites there, then use `restriction_hom_ext` to cancel restriction.
For `fullPullback_naturality`, choose an upper chart of the two independently
selected targets, then an upper chart also containing the larger admissible
target. The preceding equation and the characterizing factorization formulas
prove the two-variable restriction square after restriction from that upper
chart. Cancellation proves equality of the original bounded maps.
`fullPullback_selected` recovers the exact input map using the corresponding
recovery theorem for `localHom`.

`toStrongHom` now packages the constructed continuous map, target-containment
witnesses, every admissible pullback, spectrum squares and full two-variable
naturality in the published `StrongHom` type.
`toStrongHom_baseMap` and `toStrongHom_pullback_selected` record its ambient
map and selected bounded maps.

`RealizedBy d f` asks only that `f` admit the selected chart pairs and have the
supplied bounded pullbacks there. `toStrongHom_realizedBy` proves this for the
constructor. `RealizedBy.baseMap_eq` derives equality of ambient maps from
the chart formulas and `baseMap_unique`.
`RealizedBy.eq_toStrongHom` then proves equality of the entire strong maps.
After identifying base maps, naturality of `f` compares any admissible
pullback and its selected pullback in a common upper chart. The selected
equality and `fullPullback_comp_restriction` identify those composites, and
bounded restriction cancellation identifies the pullbacks themselves.
Strong-map extensionality finishes the proof. Thus `existsUnique_strongHom`
provides existence and uniqueness without taking an ambient map as input.
Point-map equality is used for the ambient component only; equality of
bounded algebra maps follows by algebraic cancellation and retains information
on nonreduced algebras.

`StrongHom.toLocalChartMapData` extracts these data from an existing strong
map and any admissible target selection `σ`, with no monotonicity requirement.
Directedness supplies a common upper chart; full strong naturality and its
fixed-source specialization give the local compatibility equation.
`toLocalChartMapData_realizedBy` records the original map's realization,
`toLocalChartMapData_toStrongHom` recovers the complete original strong map
by uniqueness, and `toLocalChartMapData_baseMap` recovers its continuous map.
In particular, different admissible selections from the same strong map
reconstruct that same map. The local data contain redundant choices; no
bijection between that data type and the strong morphism type is asserted.

`Hom.toLocalChartMapData` also extracts the selected bounded maps of an
existing chosen arrow. Its original monotonicity provides the common upper
chart needed for local compatibility. `Hom.toLocalChartMapData_baseMap`
recovers the original ambient map by the colimit uniqueness theorem.
`Hom.toLocalChartMapData_toStrongHom` identifies the new reconstruction with
the published `StrongHom.ofDirected`, as equality of full strong morphisms,
using that constructor's selected-pullback recovery and realization uniqueness.

The original conventions are V. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), section 1.1 and Lemma 1.1.1(i),
printed pp.13–14 / PDF pp.10–11; Definition 1.2.3 and Remark 1.2.4(i),
printed p.16 / PDF p.13; and Definition 1.2.7, printed p.18 / PDF p.15.
The source is registered as `berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Those pages were reread for this unit. The first passage supplies the
chartwise topology underlying the imported spectrum colimit; the second
supplies actual atlas domains and bounded restrictions; the last specifies
the continuous map and compatible morphisms at every admissible chart pair.
The reconstruction here is derived infrastructure under the explicit extra
directed-target hypothesis, rather than a theorem stated verbatim in the
source. Its proof combines the already published actual topological colimit
and bounded domain-factorization constructions.

The supplied atlas objects remain inputs. General atlas extension and
refinement, finite algebraic gluing, unrestricted strong composition and
localization, structure sheaves, étale and equivariant sites, and the Harris
tower remain separate construction obligations. This unit does not implement
the unrestricted extension or composition arguments following Definition
1.2.7.
