# Varying-dimensional charts on actual smooth-space rational points

This is derived construction content supporting the analytic-manifold clause of
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.15, Proposition 5.4, and the final paragraph of its proof on
printed p.16. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad allows smooth spaces whose dimensions vary between components. The
explicit atlas construction here joins the Library's actual dimension pieces
to its family of pure-dimensional charted spaces. The source does not
separately state this construction or these coordinate predicates.

All declarations are in
`Langlands.AlgebraicGeometry.AlgebraicSpace`. Let `K : Type u` be a
nontrivially normed field, let `X` be an actual algebraic space over `Spec K`,
and let `hX : SmoothOverBase X`. The underlying point set throughout is the
original `RingPoints K X K`, consisting of actual scheme-test sections. Its
topology is always the independently defined `etaleChartTopology K X`.
The coordinate space in dimension `n` is `Fin n → K` with its usual topology
and normed-space structure.

## Atlas data and analytic predicates

`DimensionPointAtlas hX` has a set of open partial homeomorphisms into `Kⁿ`
for every natural number `n`. Its selected chart at `x` has dimension
`SmoothDimensionPieces.fieldPointDimension hX x`. The fields
`mem_chart_source` and `chart_mem_atlas` give coverage by these selected
charts. The field `source_dimension` requires every chart of dimension `n`
to have source contained in the intrinsic dimension-`n` locus.

The short intrinsic lemmas `DimensionPointAtlas.covers` and
`DimensionPointAtlas.disjoint_sources` respectively expose this coverage
and prove disjointness of chart sources with different dimensions. The latter
compares the two intrinsic dimensions of a hypothetical point in their
intersection.

The following are Prop-valued definitions, rather than asserted existence
or compatibility theorems:

- `A.IsAnalytic` requires `ContDiffOn K ω` of the actual coordinate transition
  `e.symm.trans e'` on its full source for every two dimension-`n` charts.
  Different dimensions have disjoint sources by the intrinsic lemma.
- `A.AnalyticOn B f s` includes `ContinuousOn f s` for the original
  étale-chart topologies. For every source dimension `n`, target dimension
  `m`, source chart `e` and target chart `e'`, it also requires
  `ContDiffOn K ω (e' ∘ f ∘ e.symm)` on
  `e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' e'.source)`.
  Thus every target-chart intersection is retained, including target pieces
  of different dimension. Continuity is an independent part of the definition:
  these restricted coordinate tests alone would not exclude discontinuous
  jumps between target pieces.
- `A.AnalyticMap B f` is `AnalyticOn` on the whole original point set.
- `A.IsLocalAnalyticIso B f` requires preservation of the intrinsic point
  dimension and, at every source point, an actual open partial homeomorphism
  between the original point spaces agreeing with `f` on its source. That
  branch is analytic on its source, and its inverse is analytic on its target,
  using the preceding predicates.
- `A.Equivalent B` requires the actual identity map to be analytic in both
  directions. It expresses agreement of analytic structures independently
  of the chosen chart sets.

Here `ω` is Mathlib's analytic differentiability class. There is no fixed
global dimension, finiteness of the set of dimensions, quasi-compactness or
completeness hypothesis in these definitions.

## Concrete construction from the pure-dimensional family

Let `σ : AnalyticPointStructure K` be a supplied family of charted spaces.
It need not be assumed analytic for the construction. Separately assume
`hK : IsHenselianValuedField K`, `hqs : IsQuasiSeparated X` and
`hls : IsLocallySeparated X`.

`AnalyticPointStructure.dimensionPiece_isOpenEmbedding hK hX hqs n` applies
the published `isOpenEmbedding_ringPointsMap` to the actual open immersion
`SmoothDimensionPieces.inclusion hX n`. The source and target have local
finite type by their structural smoothness; quasi-separatedness of the piece
is inherited from `hqs`. This lemma uses no local separatedness or
completeness hypothesis.

`liftDimensionChart hK hX hqs n` applies Mathlib's
`OpenPartialHomeomorph.lift_openEmbedding` to this genuine inclusion on
rational points. Its source is the image of the old chart source in
`X(K)`, which is open in the original topology, and its target is the
unchanged open subset of `Kⁿ`. The only nonemptiness required by this
Mathlib construction is that of `Kⁿ`, which is inhabited also for `n = 0`.
Empty algebraic dimension pieces therefore cause no exception.

`σ.dimensionAtlasCharts hK hX hqs hls n` lifts every chart of the supplied
`σ.chartedSpace` on the actual piece `SmoothDimensionPieces.space hX n`.
The published `space_isSmoothPureDimensional` supplies that charted space's
geometric hypothesis. `σ.dimensionChartAt hK hX hqs hls x` lifts its
selected chart at the actual section
`SmoothDimensionPieces.fieldPointFactor hX x`.

`σ.dimensionAtlas hK hX hqs hls` combines these data into a
`DimensionPointAtlas hX` on the original point set. Membership in the
selected lifted source follows from the original chart coverage and
`fieldPointFactor_map`. Atlas membership follows from the supplied
pure-dimensional atlas. The source-dimension law follows from
`fieldPointDimension_map_inclusion`. These are proofs of the data's
intrinsic laws; no analytic-existence or map-compatibility law is assumed
as a field of this construction.

Finally, `liftDimensionChart_transition` identifies the transition of any
two lifted charts from the same piece with their original coordinate
transition exactly, using Mathlib's `lift_openEmbedding_trans`.

The construction uses the published open-embedding theorem directly.
It does not transport a topology along the dimension-section equivalence
or require a separate homeomorphism statement as an assumption.

## Scope and related modules

This module constructs topological charts and defines the analytic predicates.
It does not prove analyticity of the assembled atlas, functoriality of maps
across arbitrary target pieces, étale dimension preservation and analytic
local isomorphisms, scheme agreement or uniqueness of the assembled
analytic structure. Those are separate statements, proved in
`SmoothSourceDimensionAnalyticAssemblyProof`,
`SmoothSourceDimensionAnalyticFunctorialityProof`,
`SmoothSourceDimensionEtaleAnalyticIsoProof`,
`SmoothSourceDimensionAffineAgreement` and
`SmoothSourceDimensionAnalyticUniquenessProof`.
The corrected Proposition 5.4 class of smooth, quasi-separated, locally
separated spaces over complete fields remains the intended application,
with all dimension pieces included. This construction alone does not
discharge that assertion; `smoothSourceAnalyticManifold` in
`SmoothSourceAnalyticManifoldProof` proves it.
