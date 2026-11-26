# Normalized real gap growth from the two-scale chart reflection

`RealGapGrowthFromSeparatedThetaStatement` (namespace `RealGapMellinWeights`): let `F`, `Fd` be
a.e. strongly measurable functions on s-finite measure spaces (Lean's `SFinite`: countable sums
of finite measures) with two positive measurable
determinant variables each, `δ, η` and `δd, ηd`, such that `‖F‖ (δη)^z` and `‖Fd‖ (δd ηd)^z` are
integrable for all real `z ≥ σ`. Assume `sign ≠ 0`, the phase identity of
`RealGapMellinWeightsStatement`, and the separated two-scale identity: for all `β, γ > 0`

`phase · separatedTheta μ F δ η f₁ f₂ β γ = (βγ) · separatedTheta ν Fd δd ηd k₁ k₂ β⁻¹ γ⁻¹`,

with `f₁ = ordinaryWeight ds es b₁ c hc sign₁ (1/2) 0`, `f₂ = ordinaryWeight [d] es b₂ c hc sign₂ (1/2) 0`,
`k₁ = reflectedWeight dds ees (1/2) 0`, `k₂ = reflectedWeight [dd] ees (1/2) 0`. Then for any `I`,
`Id` agreeing on a right half-plane with `s ↦ ∫ F (δη)^s` and `s ↦ ∫ Fd (δd ηd)^s`,

`HasRealPairNormalizedGrowth (d :: ds) es (dd :: dds) ees b c hc sign I Id`.

## Proof

The phase is moved into the first ordinary weight. The Library's
`archimedeanMellinConvolutionReflection` integrates the separated identity over the logarithmic
scale and gives the one-scale theta identity for the convolved weights `gapOrdinaryWeight` and
`gapReflectedWeight` against the product determinants. `realGapMellinWeights` gives their
Mellin transforms, and `realThetaNormalizedGrowth` gives the normalized growth package for the
chart integrals, which `normalizedGrowth_congr_right` transfers to `I`, `Id`.

This is the real counterpart of the Library's `ComplexGapGrowthFromSeparatedTheta`, the final
Mellin step of the larger-gap recurrence in Jacquet, *Archimedean Rankin–Selberg Integrals*
(2009), §10.3.
