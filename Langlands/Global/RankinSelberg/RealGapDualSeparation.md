# Fubini and the quotient shear on the full real dual chart

This module is the real counterpart of the Library's `ComplexGapDualSeparation`; `RealGapDualMellin`
continues the same namespace.

`dualSeparatedKernel a c T W V f₁ f₂` is, on the quotient and the dual chart, the product of the inverse
character at the long Weyl determinant `det w_(q+1)`, the retained coefficient of `RealGapSeparatedKernels`,
the smaller dual kernel `weightedDual` of the right translates `ρ(C⁻¹) W` and `ρ(z) V` with weight `f₁`,
the square weight `realAdjacentMatrixWeight c⁻¹ (realRectangularSchwartzFourier a Ξ) 0` at the inverse
transpose of the leading matrix `z`, and `f₂` at its absolute determinant; here `C` is the retained matrix
and `Ξ = leadingRestriction C T.leading`.

`RealGapDualSeparationStatement` (proved by `realGapDualSeparation`): for Haar `η₁`, `κ`, a Schwartz
`Fs = T.squareEval`, functions `W` and `V` with the left characters of `−a` and `a`, and profiles `f₁`,
`f₂`: if `dualChartWeightedKernel` for the dual functions of `W` and `V` is integrable on the quotient,
the complementary rectangle and `dualChartMeasure`, then `dualSeparatedKernel` is integrable on the
quotient and `dualChartMeasure`, and the two integrals are equal.

## Proof

The quotient is translated on the right by the inverse transpose of the leading matrix
(`measurePreserving_quotientShift`), and `interchangeMiddle` puts the complementary rectangle innermost; both
preserve the product measure. At a representative `g`, `ordinaryKernel_mk` evaluates the kernel, and the
leading determinant cancels in the first profile. After the reindexing `rectangleRows`, the rectangle
integral is `unitDualKernel_separate` at `s = 0`, and `dualKernel_mk` and `translated_dualPoint` identify the
remaining Whittaker values with the smaller dual kernel of the translates. Fubini then gives the identity.

This is the separation of the dual integral after the change of variables (10.9) in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §10.3, pp. 75–76, in the absolutely convergent form of
§10.4, pp. 77–81.
