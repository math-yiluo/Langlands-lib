# Analyticity of the actual varying-dimensional atlas

This proof implements the derived chart-assembly statement
`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAnalyticAssemblyStatement`
without changing its hypotheses or its atlas. The theorem
`smoothSourceDimensionAnalyticAssembly` has this exact type in every universe `u`.

The field `K` is nontrivially normed and henselian. The actual algebraic space
`X` over `Spec K` is smooth, quasi-separated and locally separated. The
supplied family `σ : AnalyticPointStructure K` satisfies `σ.IsAnalytic`.

For every dimension `n`, the proof installs the supplied analytic manifold
structure on the genuine algebraic piece `SmoothDimensionPieces.space hX n`.
It takes two arbitrary charts in the assembled dimension-`n` atlas and obtains
their original atlas charts from the image defining `dimensionAtlasCharts`.
The equality `liftDimensionChart_transition` then replaces their entire lifted
coordinate transition, including its source, by the original piece transition.
`StructureGroupoid.compatible` places that transition in
`contDiffGroupoid ω` for the identity model on `Fin n → K`. Its forward
condition, with the identity model simplified, is precisely `ContDiffOn K ω`
on the full transition source.

This argument applies to every natural-number dimension, including zero and
empty pieces. It uses the original rational-point carrier and
`etaleChartTopology`, retains the premise `σ.IsAnalytic`, and adds no
completeness, quasi-compactness or finite dimension-range assumption.

The construction and statement are derived supporting content for Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.15, Proposition 5.4, and the final proof paragraph on printed
p.16. Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Those two printed pages were checked against the registered original.
Conrad constructs the analytic structure by transporting scheme charts and
checking their transitions. Assembly over the Library's intrinsic dimension
pieces is derived supporting content; the implemented proof is the
chart-lifting argument described above.
