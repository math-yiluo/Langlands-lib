# The real normalized pair with growth from its theta reflection

## Inverse epsilon factors

`stripExpType_inv_block_epsilon` (private) computes the inverse of the epsilon factor of a real
block from its explicit formula: for a character block it is a constant times
`|a|^{-(s-1)}`, for an induced block a constant times `|a|^{-2(s-1)}`; hence it has exponential
type on vertical strips. Products over lists follow. `stripExpType_pairReflectionFactor_inv`:
the inverse of `pairReflectionFactor ds es b c hc sign` (module `RealWeightedKernelReflection`)
has exponential type on vertical strips.

## Statement

`RealThetaNormalizedGrowthStatement`: let `F`, `Fd` be a.e. strongly measurable functions on
s-finite measure spaces (Lean's `SFinite`: countable sums of finite measures) with positive
measurable Mellin variables `δ`, `δd` such that
`‖F‖ δ^x` and `‖Fd‖ δd^x` are integrable for all real `x ≥ σ`. Let `f`, `fd` be measurable rapidly
decreasing weights with
`mellin f (-s) = (realPairLFactor ds es).denominator s · pairReflectionFactor ds es b c hc sign s · e^{s²}`
and `mellin fd (s - 1) = (realPairLFactor dds ees).denominator (1 - s) · e^{s²}`, and `sign ≠ 0`.
If `theta μ F δ f β = β · theta ν Fd δd fd β⁻¹` for all `β > 0`, then
`HasRealPairNormalizedGrowth ds es dds ees b c hc sign` holds for the Mellin transforms
`s ↦ ∫ F δ^s` and `s ↦ ∫ Fd δd^s`.

`realThetaNormalizedGrowth` proves it from the Library's `archimedeanThetaNormalizedGrowth`
with the reciprocal `L`-factor denominators (exponential type by `realLFactor_stripExpType`) and
the reflection factor and its inverse (above).

`normalizedGrowth_congr_right`: the normalized growth package transfers along agreement on a
right half-plane (`HasRealPairNormalizedGrowth.congr`).

This is the real counterpart of the generic part of the Library's
`ComplexThetaNormalizedGrowth`; it is an internal step of the Mellin argument of Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), §10.3.
