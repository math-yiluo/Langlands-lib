# Actual source refinements subordinate to a target subatlas

This module constructs a source subatlas for a strong map whose target is
restricted to a locally refining selection of original charts. It proves the
required local refinement from actual inverse-image affinoid domains and
continuity. The resulting strong map retains every original admissible bounded
pullback.

## Hypotheses and provenance

The field `K` is a complete ultrametric normed field; its valuation may be trivial.
The presentations `A` and `B` have ambient universe `v` and independently chosen
chart-index universe `w`. The map `f : StrongHom A B` includes its actual bounded
pullbacks and structural equations.

The source hypothesis `ha : A.atlas.HasAllLocalDomains` says that every ambient
subset represented by a full local domain is already the range of an original
source chart. It does not supply the desired source refinement or any output
map. `SaturatedAtlasDomainClosure.saturatedAtlas_hasAllLocalDomains` proves this
property for the previously constructed saturated atlas.

The target predicate `P` satisfies `B.atlas.IsLocallyRefiningSelection P`.
Concretely, inside each original target chart and at each of its points, finitely
many selected original charts lie inside that chart, all contain the point, and
their union is a relative neighborhood of the point. The construction proves
the corresponding source property; it does not assume it.

This is an internal construction. `StrongLocalDomainInverseImage` supplies actual
pushout domains and their exact ambient loci. `SaturatedChartCoverRefinement`
supplies original-chart representatives and bounded comparison isomorphisms,
proved using full domain factorization against every presented affinoid test.
`AtlasSubatlas` constructs an atlas from a locally refining selection, retaining
its original algebras and restrictions. `StrongAtlasQuasiIsomorphisms` supplies
the actual strong inclusions and their full quasi-isomorphism proof. No new
external-literature assertion is attributed here.

## Actual inverse-image chart representatives

For a source local domain `U`, an original target chart `j` containing its entire
image, and an original target chart `k` contained in `j`, the module uses
`B.atlas.restrictionDomain k j hk`. Its algebra is the original algebra of `k`,
and its structural map is the original bounded restriction from `j` to `k`.

`localDomainInverseImage_originalChart_locus` proves that the actual inverse-image
domain has ambient locus

```text
U.locus ∩ f.baseMap ⁻¹' range (B.atlas.chart k).
```

The proof specializes the exact inverse-image formula to the original relative
chart domain and uses containment of `k` in `j` to simplify its ambient image.
The underlying algebra remains the actual affinoid pushout of the local bounded
map and that restriction, extended through `U`.

`inverseImageOriginalChart` applies `ha.domainChartIndex` to this constructed full
domain. `range_inverseImageOriginalChart` identifies the chosen original source
chart's entire range with the displayed intersection.
`inverseImageOriginalChartDomainIso` retains the actual isomorphism of full
domains over the original source parent algebra. Its comparison maps are bounded
algebra maps obtained from full universal properties. The replacement therefore
retains algebraic data as well as its ambient subset.

If `P k`, `inverseImageOriginalChart_selected` proves that this source chart
belongs to `sourceSelectionForTarget P`. That predicate selects exactly those
original source charts whose entire image lies in some original target chart
satisfying `P`.

## Proving the source selection is locally refining

`sourceSelectionForTarget_locallyRefining` starts with an original source chart
`i` and a point `x` in its range `T`. The original `f.target_exists i` chooses a
target chart `j` containing the entire image of `T`. The target local refinement
gives a finite family `σ` of selected chart ranges inside `j`, each containing
`f(x)`, whose union is a relative neighborhood there.

The proof forms the finite image family

```text
δ = { T ∩ f.baseMap ⁻¹' V | V ∈ σ }.
```

For each member it takes `U` to be the whole full domain of source chart `i` and
uses the preceding actual inverse-image construction and `ha` to obtain an
original source chart with exactly that range. The chart belongs to
`sourceSelectionForTarget P`; its range lies inside `T` and contains `x`.

The union of `δ` equals `T ∩ f.baseMap ⁻¹' ⋃₀ σ`. Continuity of `f.baseMap`,
together with the containing-target-chart condition, pulls the relative target
neighborhood back to a relative neighborhood in `T`. Intersecting with `T`
preserves membership in the relative neighborhood filter. These facts establish
the required local refinement. This argument uses pointwise finite
neighborhoods and makes no compactness assertion about arbitrary whole chart
intersections.

## The constructed presentations and strong maps

`targetSubatlasSource ha P hP` is the actual subpresentation of `A` selected by
`sourceSelectionForTarget P`, using the refinement just proved. Its underlying
topological space is exactly `A.space`; its chart algebras, embeddings,
restrictions and domain factorization laws are inherited from the selected
original charts.

`targetSubatlasLift ha P hP` maps this source to `B.subpresentation P hP`.
Its ambient continuous map is `f.baseMap`. The source selection supplies a
containing selected target chart for every source chart. At every admissible
source and target pair, its bounded pullback is literally
`f.pullback i.val j.val h`; the chart and restriction equations are the original
ones. The two explicit recovery lemmas record these equalities.

`targetSubatlasSourceInclusion` is the actual same-space strong inclusion into
`A`. Its ambient map is the identity and its bounded maps are the original
source atlas restrictions.
`isQuasiIso_targetSubatlasSourceInclusion` reuses the full quasi-isomorphism
theorem for locally refining subatlases, including full domain representation
for every admissible chart pair. If `f` itself is a full quasi-isomorphism,
`IsQuasiIso.targetSubatlasLift` proves the same for the constructed lift: it
retains the ambient homeomorphism and each selected original local
representation.

## Scope

The construction requires source closure under all local full domains and the
stated target local-refinement condition. It requires no coherence law on `f`,
directedness, upper cofinality, nontrivial valuation, or global finite chart
cover. This module does not construct composition in a strong-map category,
prove a categorical Ore square, handle an arbitrary target quasi-isomorphism,
identify the full analytic category, or construct analytic/equivariant sites or
Harris tower specializations. These remain separate obligations of the host
task.
