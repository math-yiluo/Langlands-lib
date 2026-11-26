# Common product-determinant moments on the full real dual chart

This module is the real counterpart of the Library's `ComplexGapDualPowerMoment`.

`RealGapDualPowerMomentStatement` (proved by `realGapDualPowerMoment`): under the hypotheses of
`RealGapDualHaarStatement` (Haar `η₁`, inversion-invariant Haar `κ`, `Wd` and `Vd` in the uniform models
at `a` and `−a`, `Fs = T.squareEval`), there is `σ` such that for every `s ∈ ℂ` with `σ ≤ Re s` the dual
chart kernel with both profiles `x ↦ x^s` is integrable for the quotient measure times the complementary
rectangle times `dualChartMeasure`.

The proof applies `realGapDualHaarPowerBounds` with the bounds `‖x^s‖ = x^{Re s}` for `x > 0` and takes
`σ` the larger of its two thresholds. These are the absolute product-determinant moments used for the
Mellin integration in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.4, pp. 77–81.
