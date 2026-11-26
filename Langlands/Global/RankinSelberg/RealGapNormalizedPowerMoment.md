# Diagonal Mellin moments on the normalized ordinary real gap chart

This module is the real counterpart of the Library's `ComplexGapNormalizedPowerMoment`; its declarations lie
in the namespace `Langlands.Global.RankinSelbergGlobal.RealGapNormalizedWeighted`.

`RealGapNormalizedPowerMomentStatement` (proved by `realGapNormalizedPowerMoment`): for `W` in
`realUniformWhittakerModel (t + 1 + q) ds (−a)`, `V` in `realUniformWhittakerModel t es a`, Haar measures `η₁`,
`κ` and `β ∈ ℝ`, there is `σ₀` such that for `σ ≥ σ₀`, all Schwartz tests and every measurable `w` with
`‖w p‖ ≤ δ(h)^β`, the kernel `normalizedWeightedKernel false … 0 (x ↦ x^σ) (x ↦ x^σ) w` is integrable for
`normalizedGapMeasure t q a D (dirac 0) η₁ κ`. The proof specializes `realGapNormalizedPowerBounds` (with the
Dirac measure at the zero rectangle, `s = 0`, `b = 0`) at `σ₀ = max(0, u, v)`.

This is the ordinary chart moment used for the absolute Fubini argument in the larger-gap recurrence of
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
