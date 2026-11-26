# Weighted reflection for the real pair factors

Fix real block lists `ds`, `es` and lists `dds`, `ees` for the reflected side, an epsilon
parameter `b ∈ ℝˣ`, a positive scale `c` and a sign `sign ∈ ℂ`.

## Definitions

* `pairReflectionFactor ds es b c hc sign s = sign · realPairEpsilon ds es b c hc s`. It is
  entire (`differentiable_pairReflectionFactor`) and of exponential type on vertical strips
  (`stripExpType_pairReflectionFactor`, from `realEpsilon_stripExpType`).
* `ordinaryWeight ds es b c hc sign rate B` is the inverse Mellin transform (on the line
  `Re = 0`) of the Library's `gaussianOrdinaryTransform` of the reciprocal pair `L`-factor
  denominator `(realPairLFactor ds es).denominator` and the reflection factor, with Gaussian rate
  `rate > 0` and real shift `B`.
* `reflectedWeight dds ees rate B` is the inverse Mellin transform of
  `gaussianReflectedTransform` of `(realPairLFactor dds ees).denominator`.
* `realWeights_data`: both weights are measurable and rapidly decreasing, and
  `mellin f (-s) = L(ds × es)(s)⁻¹-denominator · E(s) · gaussianFactor rate B s`,
  `mellin fd (s - 1) = L(dds × ees)-denominator (1 - s) · gaussianFactor rate B s`
  (`archimedeanGaussianMellinPair`).

## Statement

`RealWeightedKernelReflectionStatement`: let `K s x = K 0 x · δ(x)^s` and `L s y = L 0 y · η(y)^s`
be kernels on s-finite measure spaces (Lean's `SFinite`: countable sums of finite measures) with
positive measurable Mellin variables `δ`, `η`, both
integrable on some right half-plane. If the integrals `I(s) = ∫ K s`, `Id(s) = ∫ L s` satisfy
`HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id`, then for every rate `> 0`, shift `B`
and `β > 0`

`theta μ (K 0) δ (ordinaryWeight …) β = β · theta ν (L 0) η (reflectedWeight …) β⁻¹`.

`realWeightedKernelReflection` proves it.

## Proof

Choose a vertical line in the common region of convergence and of agreement of the normalized
functions. The determinant powers there give integrable moments and recover measurability of the
kernels at `s = 0` (`kernel_zero_eq`, `norm_kernel`).
`stripExpType_of_hasStripExponentialGrowth`: continuity extends the large-height exponential
bounds of the normalized functions to the whole strip. With the Gaussian factor this gives the
decay needed by the Library's contour comparison `theta_mellinInv_reflection`, which yields the
identity.

This is the real counterpart of the Library's `ComplexWeightedKernelReflection` (whose
normalization fixes the reflected lists to the inverse characters and the scale to `‖a‖`); here
the reflected lists, the epsilon parameter and the scale are arbitrary. It is an internal step of
the Mellin argument in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §10.3, with the
Gaussian normalization of the Library's Archimedean Mellin modules.
