# The real dual zeta integral on the separated determinant chart

This module continues the namespace `RealGapDualSeparation`; it is the real counterpart of the Library's
`ComplexGapDualMellin`.

`dualLeadingDet` is the absolute determinant of the inverse transpose of the leading matrix and
`dualProductDet` its product with the quotient determinant; both are positive and measurable.
`dualSeparatedKernel_mul_profiles` writes the separated kernel as its unit-profile kernel times the two
profiles at these variables.

`RealGapDualMellinStatement` (proved by `realGapDualMellin`): let `η₁`, `κ` be Haar measures with `κ`
inversion invariant, `C ∈ ℂ`, `Fs = T.squareEval`, `W` in `realUniformWhittakerModel (t+1+q) ds (−a)`, `V`
in `realUniformWhittakerModel t es a`, with dual functions in `realUniformWhittakerModel (t+1+q) dds a` and
`realUniformWhittakerModel t ees (−a)`, and let `U` on `GL_(t+1+q+2)(ℝ)` satisfy the dual restriction formula
`Ũ(rectangularPoint g x · unfoldingWeyl) = P g (1/2) · C · ∫ unitDualKernel … ∂dualChartMeasure`. Then the
unit-profile separated kernel `F` is a.e. strongly measurable, and there is `σ` such that for `σ ≤ Re s`
the moment `‖F‖ · dualProductDet^{Re s}` is integrable and
`realUnequalDualIntegral (rankLT t (q+1)) (−a) D U V s = C · ∫ F · dualProductDet^s`.

## Proof

On the unintegrated chart the two profiles `x^s` multiply to the power of the quotient determinant
(`dualChartPower_eq`). `realGapDualPowerMoment` gives joint integrability, `realGapDualSeparation` passes to
the separated kernel, and the half power in the restriction formula combines with the Mellin shift
(`detPower_add`). `RealJacquet.selfDualMeasure_neg` identifies the measures for `−a` and `a`. Dividing a
power-weighted integrable kernel by its nonzero power gives measurability of `F`.

This relates the dual integral to the separated variables in Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §10.3, (10.9), pp. 75–76, and §10.4, pp. 77–81.
