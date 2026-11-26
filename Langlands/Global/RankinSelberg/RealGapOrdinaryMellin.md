# The real ordinary zeta integral on the separated determinant chart

This module continues the namespace `RealGapOrdinarySeparation`; it is the real counterpart of the
Library's `ComplexGapOrdinaryMellin`.

`ordinaryProductDet` is the product of the quotient determinant and the absolute determinant of the leading
matrix. `ordinaryMellinData`: for `W` in `realUniformWhittakerModel (t+1+q) ds (−a)` and `V` in
`realUniformWhittakerModel t es a`, the ordinary unit-profile separated kernel `F` is a.e. strongly
measurable on the quotient and `ordinaryChartMeasure`, and `‖F‖ · ordinaryProductDet^x` is integrable for
all large real `x`.

`RealGapOrdinaryMellinStatement` (proved by `realGapOrdinaryMellin`): if `U₀` on `GL_(t+1+q+2)(ℝ)`
satisfies the ordinary restriction formula
`U₀(pad g) = P g (1/2) · C · ∫∫ unitOrdinaryKernel a c T W g p Z dZ dp` for some `C ∈ ℂ`, then besides these
moments `realUnequalIntegral (rankLT t (q+1)) D U₀ V s = C · ∫ F · ordinaryProductDet^s` for all large `Re s`.

## Proof

`realGapNormalizedPowerMoment` with the Dirac rectangle and `realGapOrdinarySeparation` give the moments
with equal real powers of the two determinant variables; dividing by the nonzero power gives
measurability. The inverse right quotient shear by the leading matrix `z` replaces a representative `g` by
`g z⁻¹` (`ordinaryKernel_shift`), and the two determinant variables then multiply to the original quotient
determinant. At spectral parameter zero `unitOrdinaryKernel_separate` gives the separated factors, and the
half power of the restriction formula turns the larger Mellin shift into the smaller one. The common
absolute moment justifies Fubini, and measure preservation of the shear finishes the identity.

This is the ordinary integral of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.3,
Lemma 10.3, p. 74, in the absolutely convergent form of §10.4, pp. 77–78.
