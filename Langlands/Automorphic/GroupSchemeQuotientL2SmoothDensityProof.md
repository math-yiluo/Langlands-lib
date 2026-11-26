# Archimedean and simultaneous smooth density on the positive-torus quotient

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeQuotientL2SmoothDensity`
proves `GroupSchemeQuotientL2SmoothDensityStatement` in every universe `u`.
Its type is exactly that proposition: the original positive-torus quotient
`Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)` with its published
right actions. The hypotheses keep the split central torus data and right
invariance of the norm-one Haar measure. No split or quasi-split hypothesis
on `G` occurs.

## Archimedean density

The proof fixes the completion scalar instances, the reductive atlas
`InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG` and the Lie group
structure `InfiniteAdelicGroupPoints.reductiveLieGroup F G hG` on the infinite
adelic group points, modelled on
`InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension`. It takes the
left Haar measure `Measure.haar` on that group. The infinite action
`haarQuotientL2InfiniteRightAction` preserves norms
(`norm_haarQuotientL2InfiniteRightAction`). Its orbit maps are continuous
(`continuous_haarQuotientL2InfiniteOrbit`) and almost everywhere strongly
measurable (`haarQuotientL2InfiniteOrbit_aestronglyMeasurable`). These are
the hypotheses of `Langlands.Analysis.integratedIsometricSmoothDensity`, the
proof of `IntegratedIsometricSmoothDensityStatement`. Applying it gives the
first conjunct: the real-manifold smooth vectors of the infinite action are
norm dense.

## Simultaneous density

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeQuotientL2FiniteApproximation`,
the proof of `GroupSchemeQuotientL2FiniteApproximationStatement`, supplies compact open subgroups
`K n` of the finite adelic group points and the averages
`haarQuotientL2FiniteAverage F G T i hi I e hc (K n)`. Each average has image
fixed by `K n` under `haarQuotientL2FiniteRightAction`, and for every vector
the averages converge to it in norm.

Fix a vector `φ` and `ε > 0`. By the first conjunct there is an archimedean
smooth vector `ψ` with `dist φ ψ < ε / 2`. Choose `n` with
`dist (A ψ) ψ < ε / 2`, where `A` is the average over `K n`. Three facts
hold for `A ψ`:

- `A ψ` is fixed by the open subgroup `K n`. That is the witness for
  `Langlands.IsSmoothVector` of the finite action.
- `A` commutes with every infinite translation
  (`haarQuotientL2FiniteAverage_infiniteRightAction`). It is a continuous
  linear map, so
  `Langlands.Global.RestrictionSplitCentre.isSmoothVector_of_intertwining`
  carries the archimedean smooth vector `ψ` to an archimedean smooth vector
  `A ψ`.
- The triangle inequality gives `dist φ (A ψ) < ε`.

So every norm ball around `φ` meets the set of simultaneously smooth
vectors, which is the second conjunct.

## Provenance

The quotient convention follows Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), §2.6, (2.19)–(2.22), printed
pp. 68–69 (PDF pp. 85–86), `getz-hahn-2024-automorphic-representations`,
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The density argument is not taken from that source. It applies two Library
results to this quotient: the integrated smoothing proof
`integratedIsometricSmoothDensity` and the finite averaging proof
`groupSchemeQuotientL2FiniteApproximation`.
