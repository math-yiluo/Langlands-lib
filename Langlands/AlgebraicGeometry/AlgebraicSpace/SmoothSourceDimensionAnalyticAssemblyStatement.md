# Analytic assembly across actual smooth dimension pieces

Author: Worker 3519.

This derived statement supports Brian Conrad, *Weil and Grothendieck
approaches to adelic points*, December 31, 2011, printed p.15,
Proposition 5.4, and the final paragraph of its proof on printed p.16.
The registered original is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad constructs the analytic structure by transporting scheme charts
and checking their transitions. The separate assembly over intrinsic
dimension pieces is supporting host content, not a numbered source
assertion. The original complete-field conclusion permits the dimension
to vary between components.

`SmoothSourceDimensionAnalyticAssemblyStatement` is a proposition definition.
It states a transition-analyticity comparison for the concrete
`AnalyticPointStructure.dimensionAtlas`; this module does not prove it.

Let `K` be any nontrivially normed henselian valued field. Let
`σ : AnalyticPointStructure K` satisfy `σ.IsAnalytic`, meaning that all its
pure-dimensional charted spaces are analytic manifolds. Let `X` be an actual
smooth algebraic space over `Spec K`, with quasi-separatedness and local
separatedness supplied separately. There is no quasi-compactness, finite
range of dimensions, positive dimension or nonempty point-space hypothesis.
Smoothness supplies local finite type. No completeness is needed for this
comparison once the analytic pure-dimensional family is supplied.

The atlas in the conclusion is the actual construction
`σ.dimensionAtlas hK hX hqs hls`. Its carrier remains `RingPoints K X K`
with the independently defined `etaleChartTopology K X`. Each of its
dimension-`n` charts is the lift of a supplied chart on the genuine
`SmoothDimensionPieces.space hX n`, along that piece's actual inclusion
on rational points. The construction covers the original point space,
proves its intrinsic dimension law, and includes every natural-number
piece, including empty pieces.

The conclusion is `DimensionPointAtlas.IsAnalytic`: for every dimension
and every ordered pair of atlas charts in that dimension, their coordinate
transition is `ContDiffOn K ω` on the entire source of the composed open
partial homeomorphism. Charts of different dimensions have disjoint
sources by the construction's intrinsic law. Both directions of each
transition are tested because the chart pair is ordered.

The intended proof uses `liftDimensionChart_transition`, which identifies
the full lifted transition, including its source, with the original
piece transition. The piece is in the existing pure-dimensional family
by `SmoothDimensionPieces.space_isSmoothPureDimensional`; `σ.IsAnalytic`
then supplies transition analyticity for every original atlas chart.
This explains why the result concerns all charts and their full domains,
without a finite-dimensional-index restriction or transported topology.

The statement retains `σ.IsAnalytic` as a premise. A complete-field
application must discharge it with the published canonical family theorem.
This unit does not state or prove functoriality across target-piece
intersections, dimension preservation for étale maps, analytic inverse
branches, scheme agreement or uniqueness of the full varying-dimensional
structure. Those remain separate obligations of Task 3519.
