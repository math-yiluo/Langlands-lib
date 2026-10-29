# Compact coset charts of an induced space

This module constructs a family of actual subsets of the balanced quotient
`Langlands.TopologicalInduction.Space H X` and proves its topological net and
compactness properties. Here `G` is a group, `H` a subgroup, and `X` an `H`-set.
The group and space may lie in independent universes. The construction imports
the published induced space and its translated charts.

## Actual family and charts

`cosetChartFamily H` is the range of

`c ↦ component H ⁻¹' {c}` for `c : G ⧸ H`.

Thus its members are the actual fibers of the left-coset map `[g,x] ↦ gH`.
`fiber_mem_cosetChartFamily` includes each fiber, and
`range_chart_mem_cosetChartFamily` includes the range of each translated chart
`x ↦ [g,x]`. The imported `range_chart_eq_fiber` identifies the fiber at `c`
with the range of the chart at the chosen representative `c.out`.
Neither the family nor these identifications require topology, subgroup
normality, a finite index, or a nonempty original space.

## Open fibers and the net

For these results `G` is a topological group, `H` is open, and `X` has a topology.
Continuity of the subgroup action on `X` is not required.

`isClopen_component_fiber` uses the discrete quotient topology on `G ⧸ H`
and continuity of `component` to prove every fiber open and closed.
`isQuasinet_cosetChartFamily` chooses the singleton consisting of the fiber
through the given point. That open fiber is a neighborhood, so it supplies
the required finite quasinet witness.

`isNet_cosetChartFamily` also proves the quasinet condition for the restricted
family on the intersection of any two members. At a point of that intersection,
the two component values are equal. The common fiber belongs to the original
family, is contained in the intersection, and restricts to the whole intersection.
The imported `isQuasinet_of_univ_mem` completes the pointwise proof. Empty
intersections impose no pointwise obligation. The result uses precisely the
actual induced subspace topology and the Library's `restrictedFamily`.

## Compact subsets meet finitely many cosets

Under the same hypotheses,
`finite_component_image_of_isCompact` proves that the image of a compact subset
under `component` is finite. It maps that subset continuously into the discrete
coset quotient and applies Mathlib's finiteness theorem for compact subsets
of discrete spaces. This finite image is exactly the set of coset labels whose
fibers meet the subset.

`exists_finite_chart_cover_of_isCompact` converts that image into a finite set
of cosets and covers the compact subset by their actual chart ranges. These
two results assume neither continuity of the action nor compactness or
Hausdorffness of `X`.

## Compact Hausdorff fibers and local compactness

Now assume that the subgroup action on `X` is continuous.
`isCompact_of_mem_cosetChartFamily` proves compactness of each member when
`X` is compact, using its identification with the image of a continuous chart.
This result does not require `H` open.

`t2Space_induced` proves that the induced space is Hausdorff if `H` is open
and `X` is Hausdorff. The proof transfers the Hausdorff topology of the
coproduct of copies of `X` along the actual `cosetCopiesHomeomorph`.
With `X` compact Hausdorff, `isCompactFamily_cosetChartFamily` combines these
results to give the Library's `IsCompactFamily`: each member is compact and
Hausdorff with its subspace topology.

Under the same assumptions, `locallyCompactSpace_induced` applies the imported
compact-quasinet local compactness theorem. Its compact neighborhoods come
from the actual compact fibers through points. Hausdorffness is supplied
separately by `t2Space_induced`. No global instance is imposed for arbitrary
subgroups; each conclusion takes the explicit openness hypothesis it needs.

## Provenance and limits

This is an internal construction derived from the published
`Topology.GroupAction.InducedCharts` and
`Geometry.Analytic.AtlasTopology.QuasinetProperties` APIs, with Mathlib's
compact-image, discrete-space and homeomorphism theorems. Berkovich,
*Etale cohomology for non-Archimedean analytic spaces* (1993), section 1.1,
printed pages 13–14 (PDF pages 10–11), supplies the quasinet and net definitions
and the compact-quasinet local compactness remark. The registered original
is `berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The Library's compact-family predicate records both compactness and
Hausdorffness, in accordance with the source's convention.

The coset-copy convention comes from the already imported induced charts,
following Berkovich's unfinished 1995–1996 manuscript *Etale equivariant
sheaves on p-adic analytic spaces*, Construction 1.1.2, printed/PDF page 2.
Its supplied folder is registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member PDF SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The compact fiber and finite-coset statements here are derived topological
results, not assertions quoted from that manuscript.

This unit supplies topology for subsequent actual induced rational spectra.
It constructs no analytic atlas, structure sheaf, analytic morphism category,
distinguished domain, etale or quasi-etale site, cohomology, or Harris tower.
