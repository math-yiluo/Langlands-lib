# Separation of the two determinant powers in the real larger-gap comparison

This module is the real counterpart of the Library's `ComplexGapSeparatedKernels`. Notation as in
`RealGapNormalizedRestriction` and `RealGapMatchedTests` with `k = t + 1`, `m = q + 1`,
`n = t + 1 + q + 1`; `P g s = |det g|^s`.

* `detPower_mul`, `detPower_add`: `P` is multiplicative in `g` and additive in `s`.
* `leadingRestriction_group`: at a group argument `h`, the leading square test
  `leadingRestriction k m k C Φ` takes the value `Φ(leading(C · A h))`.
* `retainedCoefficient a c T C = tailFactor a T C · η_c(det C)`.
* `translated_dualPoint`: the dual of the right translate `ρ(C^{-1}) W` at
  `rectangularPoint g V · unfoldingWeyl` is the dual of `W` at `lowerPoint g (rectangleRows V) · w · ι(C)^{-1}`.

`RealGapSeparatedKernelsStatement` (proved by `realGapSeparatedKernels`): let `F = squareEval T` be a
Schwartz square test. For all functions `W`, `Wd` on `GL_n(ℝ)`, `g ∈ GL_k(ℝ)`, outer data `b` with leading
matrix `z`, `Z`, `V` and `s ∈ ℂ`, with `C = retainedTail b Z` and `Ξ = leadingRestriction k m k C T.leading`:

1. `P(g z)(s − (q+1)/2) · unitOrdinaryKernel a c T W (g z) b Z =
   retainedCoefficient a c T C · (W(A g · C^{-1}) · P g (s − (q+1)/2)) · realAdjacentMatrixWeight η_c Ξ s z`;
2. `P(g ι₁(z))(s − (q+1)/2) · ∫ dualFiber a c F T Wd (g ι₁(z)) z C V X dX =
   η_{c⁻¹}(det w_m) · retainedCoefficient a c T C · (Wd(lowerPoint g V · w · ι(C)^{-1}) · P g (s − (q+1)/2)) ·
   realAdjacentMatrixWeight η_{c⁻¹} Φ̂_Ξ s (ι₁ z)`, where `Φ̂_Ξ = realRectangularSchwartzFourier a Ξ` and
   the integral is over `(q+1) × k` matrices for `rectangularMeasure (realSelfDualMeasure a)`.

On the ordinary side the shear `g ↦ g z` cancels `z` in the smaller Whittaker argument. The
determinant weight of `z` combines with the Mellin power into the square weight, because
`(k+q)/2 + s − (q+1)/2 = t/2 + s`. The retained matrix has `|det C| = 1`
(`normalizedAbs_retainedTail`), so its weight is the character value `η_c(det C)`. On the dual side
`realGapMatchedTests` integrates the complementary rectangle. The weight of `dualMatrix C z V` splits
into `η_c(det C)` (inverse transpose inverts the determinant), the inverse character at the
determinant of the long Weyl element `w_m`, and the weight of `ι₁(z)`. The ordinary identity is the
separation of the ordinary leading variable in Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§10.3, Lemma 10.3, p. 74; the dual identity is the calculation from (10.7) to (10.9), pp. 75–76.
