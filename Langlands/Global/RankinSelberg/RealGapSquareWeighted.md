# The scaled determinant identity for a fixed real square coefficient

This module is the real counterpart of the Library's `ComplexGapSquareWeighted`. Notation as in
`RealGapSquareReflection`; `δ(y) = |det y|`.

`RealGapSquareWeightedStatement` (proved by `realGapSquareWeighted`): under the hypotheses of
`RealGapSquareReflectionStatement`, for `rate > 0`, `L ∈ ℝ` and `b > 0`, with the ordinary and reflected
weights `w = ordinaryWeight [c] es a √|a| 1 rate L` and `wd = reflectedWeight ([c] dual) (es dual) rate L`
of `RealWeightedKernelReflection`,

`∫ realAdjacentMatrixWeight η_c Φ 0 y · B f (x y) · w(b δ(y)) dy =
b · ∫ realAdjacentMatrixWeight η_{c⁻¹} Φ̂ 0 (ι y) · B f (x y) · wd(b^{-1} δ(ι y)) dy`,

both integrals for `D.groupHaar`.

The proof writes both square integrands as their value at `s = 0` times `δ(y)^s`
(`matrixWeight_spectral`), which is the input form of `realWeightedKernelReflection`. That theorem
applied to the normalized pair of `realGapSquareReflection` gives the identity with the dual integrand
`realAdjacentMatrixWeight η_{c⁻¹} Φ̂ 0 y · B f (x ι(y))`. The substitution `y ↦ ι(y)` preserves
`D.groupHaar` (`realHaar_measurePreserving_inverseTranspose`), and `ι` is an involution. This is the
square comparison between (10.10) and (10.9) of Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§10.
