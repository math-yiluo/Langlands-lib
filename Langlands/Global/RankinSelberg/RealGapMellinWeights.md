# Convolved real gap weights

Let `c > 0` be a scale, `phase ∈ ℂ` a constant, `d`, `dd` real blocks and `ds`, `es`, `dds`,
`ees` real block lists, with epsilon parameters `b, b₁, b₂ ∈ ℝˣ` and signs `sign, sign₁, sign₂`.

## Definitions

* `gapOrdinaryWeight c hc phase d ds es b₁ b₂ sign₁ sign₂` is the logarithmic (Mellin)
  convolution `mellinConvolution` of `x ↦ phase · ordinaryWeight ds es b₁ c hc sign₁ (1/2) 0 x`
  with `ordinaryWeight [d] es b₂ c hc sign₂ (1/2) 0` (weights of `RealWeightedKernelReflection`
  with Gaussian rate `1/2` and shift `0`).
* `gapReflectedWeight dd dds ees` is the convolution of `reflectedWeight dds ees (1/2) 0` with
  `reflectedWeight [dd] ees (1/2) 0`.

## Statement

`RealGapMellinWeightsStatement`: suppose that for all `s`

`phase · pairReflectionFactor ds es b₁ c hc sign₁ s · pairReflectionFactor [d] es b₂ c hc sign₂ s
  = pairReflectionFactor (d :: ds) es b c hc sign s`.

Then the two convolved weights are measurable and rapidly decreasing, and

* `mellin (gapOrdinaryWeight …) (-s) = (realPairLFactor (d :: ds) es).denominator s ·
  pairReflectionFactor (d :: ds) es b c hc sign s · e^{s²}`,
* `mellin (gapReflectedWeight …) (s - 1) = (realPairLFactor (dd :: dds) ees).denominator (1 - s) · e^{s²}`.

`realGapMellinWeights` proves it: the Mellin convolution theorem
`archimedeanBinaryMellinConvolution` multiplies the two Mellin transforms, the two half-rate
Gaussian factors multiply to `e^{s²}`, and the reciprocal pair `L`-factor of `d :: ds` against
`es` splits as the product for `[d]` and for `ds` (`RealJacquet.realPairLFactor_cons_mul`).

This is the real counterpart of the Library's `ComplexGapMellinWeights`. There the phase and the
sign identity are made explicit for the complex normalization; here the identity relating the
phase and the epsilon factors is a hypothesis, to be supplied by the sign computation of the
real normalization (for example with `RealJacquet.pair_epsilon_neg` and
`RealJacquet.realPairEpsilon_cons_mul`). It is the Mellin bookkeeping of the larger-gap step of
Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §10.3.
