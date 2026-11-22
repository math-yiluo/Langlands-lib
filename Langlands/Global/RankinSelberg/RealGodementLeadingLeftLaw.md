# The left Whittaker law of the real Godement leading family at every exponent

Fix `t`, the lower group `G = GL_{t+1}(ℝ)`, the upper group `H = GL_{t+2}(ℝ)` and its upper
unipotent subgroup `N`. Let `w` be the long Weyl element of `H`. Worker 771's Library function
`godementLeadingFamily D a Φ W p g z` is the Godement column value
`godementColumnValue D a Φ W (charData p z) (w g)` of a Schwartz test `Φ` on real
`(t+1) × (t+2)` matrices, a lower coefficient `W` and the leading character `charData p z`.
This module proves that it has the left Whittaker law with character `-a` at every leading
exponent `z`.

## Statements

* `stepRectangle_mul_weylConjugate`: for `u ∈ N` and step coordinates `z`,
  `stepRectangle z · (w u w) = stepRectangle z'`, where `z'` corresponds under the step chart
  `upperStepChart` to the product of the chart image of `z` with `u`.
* `kernelSlice_weylConjugate_mul`: the Godement slice
  `kernelSlice a Φ h g = ∫ Φ(h · stepRectangle z · g) ψ_a(stepPhase z) dz` satisfies
  `kernelSlice a Φ h ((w u w) g) = χ_a(u)⁻¹ · kernelSlice a Φ h g`. Here `χ_a(u)` is the
  standard character `standardCharacter (realScaledCharacter a) (t + 1) u`, the value of `ψ_a` on
  the sum of the superdiagonal entries of `u`.
* `kernelIntegrand_weylConjugate_mul` and `quotientKernel_weylConjugate_mul`: the Godement
  outer integrand and its descent to the left unipotent quotient transform by the same factor
  `χ_a(u)⁻¹`. The determinant weight is unchanged, since `det(w u w) = 1`.
* `godementColumnValue_weylConjugate_mul`: for `W` in the uniform real Whittaker model with
  character `-a`, `godementColumnValue D a Φ W c ((w u w) g) = χ_a(u)⁻¹ · godementColumnValue D a Φ W c g`.
* `RealGodementLeadingLeftLawStatement` (proved by `realGodementLeadingLeftLaw`): for every
  quotient datum `D`, nonzero real `a`, Schwartz test `Φ` (no support condition), block list
  `ds`, `W` in `realUniformWhittakerModel t ds (-a)`, parity `p` and exponent `z`, every
  `u ∈ N` and every `g ∈ H` satisfy
  `godementLeadingFamily D a Φ W p (u g) z = realWhittakerCharacter (-a) u · godementLeadingFamily D a Φ W p g z`.

## Proof

The step chart identifies the step rectangle with the reversed rows of an upper unipotent
`(t+2) × (t+2)` matrix `U = upperStepChart z` (`stepRectangle_eq_upperStepChart`). Right
multiplication by `w u w` reverses indices on both sides
(`weylLong_conjugate_entry`). It therefore becomes right multiplication of `U` by `u`, after
reindexing the matrix-product sum by `Fin.rev`.

The phase `ψ_a(stepPhase z)` is the standard character of `U` (`stepPhase_eq_upperStepChart`).
The standard character is multiplicative, so the phase at the new coordinates is the old phase
times `χ_a(u)`. The step chart carries the step measure to the upper entry Haar measure
(`measurePreserving_upperStepChart`). That measure is right invariant
(`upperStepHaar_isMulRightInvariant`), so the coordinate change `z ↦ z'` preserves the step
measure. Changing variables gives the slice identity. This is the right-multiplication analogue
of the Library's `kernelSlice_conjugate_unipotent`.

The outer integrand is a product of determinant weights, the slice and `W`. The quotient kernel
is its descent, so it transforms by the same factor, checked on representatives. The Library's
`realGodementColumnQuotient` writes the column value as a fixed positive scale times the
quotient integral of this kernel, which gives the column-value identity. Finally,
`w (u g) = (w u w)(w g)` since `w² = 1`, and
`χ_a(u)⁻¹ = standardCharacter (realScaledCharacter (-a)) (t + 1) u = realWhittakerCharacter (-a) u`
(`standardCharacter_realScaled_neg`).

## Provenance and scope

This is the left `N`-covariance of Godement's sections in Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §8.1 (p. 54), where `W_{Φ,W',μ}` is a Whittaker function for the larger group.
The Library already has it on the dominant half-plane for additive Jacquet inputs
(`IsLeadingJacquetContinuation.leftWhittaker`). The present statement holds at every exponent
and for every lower coefficient of the uniform model. It is needed so that the generator family
`z ↦ godementLeadingFamily D a Φ W p · z` satisfies the hypotheses of the family holomorphy
theorem for real equal-rank integrals. It proves no growth, regularity, continuation or
functional equation, and does not prove `RealLocalUniformPositiveEqualContinuationStatement`.
