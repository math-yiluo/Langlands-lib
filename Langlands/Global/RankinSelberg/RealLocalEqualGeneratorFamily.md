# Regularity and holomorphy of the real Godement generator family

Fix `t`, the lower group `G = GL_{t+1}(ℝ)` and the upper group `H = GL_{t+2}(ℝ)`. The generator
family is `L(z) = (g ↦ godementLeadingFamily D a Φ U p g z)`. Here `Φ` is a Schwartz test on real
`(t+1) × (t+2)` matrices supported in a compact set `S` of full-row-rank matrices, and `U` is a
lower coefficient in the uniform real Whittaker model with character `-a`. These are the column
generators of `compactReflectedColumnGenerators`. This module is the real
counterpart of the complex module `ComplexLocalEqualGeneratorFamily`.

## Statements

* `godementLeadingFamily_mem_regularFunctions`: each `L(z)` lies in
  `RealLocalWhittaker.regularFunctions (t+1) (-a)`. That is, it has the left Whittaker law with
  character `-a`, is smooth, and has polynomial growth in the matrix height.
* `iteratedRightDerivative_godementLeadingFamily_mem`: every iterated right derivative of `L(z)`
  lies in the same space.
* `RealLocalEqualGeneratorFamilyStatement` (proved by `realLocalEqualGeneratorFamily`): fix real
  quotient data `D` and `D'` of ranks `t` and `t + 1`, nonzero reals `a` and `b`, a coefficient
  `V` of the uniform model of rank `t + 2` with character `a`, a Schwartz function `φ` on
  `ℝ^{t+2}`, and a radius `R`. Then there is `σ` with the following properties.
  * For `|z| < R` and `Re s > σ`, the integrands of the real equal-rank integral `Ψ(s; L(z), V, φ)`
    and of the dual integral `Ψ(s; L(z)~, V~, φ̂_b)` are integrable. Here `~` is the Weyl
    inverse-transpose dual and `φ̂_b = realFourierTransform b φ`.
  * `(z, s) ↦ realEqualIntegral D' (L z) V φ s` and
    `(z, s) ↦ realEqualDualIntegral b D' (L z) V φ s` are complex differentiable on
    `ball(0, R) × {Re s > σ}`.

## Proofs

Regularity of `L(z)`:

* the left law is `realGodementLeadingLeftLaw` (from `RealGodementLeadingLeftLaw`);
* smoothness is the Library's `contMDiff_godementLeadingFamily`;
* the height bound is `realGodementColumnGrowth`.

The lower regularity and uniform derivative growth needed by these come from
`realUniformWhittakerRegularity`.

For the derivatives, let `M` be the span of the members `L_Ψ(z)` for all tests `Ψ` supported in
`S`. Each element of `M` is smooth. The Library formula `rightDerivative_godementLeadingFamily`
writes the right derivative of `L_Ψ(z)` in a direction `B` as a multiple of `L_Ψ(z)` plus the
member for the rectangular variation of `Ψ`, again supported in `S`. Linearity of right
derivatives on smooth functions then shows that `M` is stable under right derivatives. By
induction on the derivative word, every iterated derivative of `L(z)` lies in `M`, and `M` is
contained in the regular functions.

For holomorphy, view `z` as a point of `Fin 1 → ℂ`. The Library theorem
`realGodementSpectralGrowth`, applied to the constant lower family `U` and the exponent `z 0`,
gives locally uniform derivative growth of the generator family.
`exists_uniform_derivativeGrowth` makes the growth uniform on the closed ball of radius `R`, and
`hasUniformGauge_of_derivativeGrowth` turns it into a uniform gauge on `ball(0, R) × ℂ`. The
coefficient `V` is a constant family with a gauge (`RealWhittakerGauge.exists_gauge_bound`).
Pointwise holomorphy in `z` is `differentiable_godementLeadingFamily`.

The family holomorphy theorem `realLocalEqualFamily` (from `RealLocalEqualFamily`) is then
applied twice, with parameter `(z, s) ∈ ℂ × ℂ` and spectral variable `s`:

* to `L` and `V`, with characters `-a` and `a`;
* to their Weyl inverse-transpose duals, with the Schwartz function equal to `φ̂_b`
  (`RealFourierSchwartz.exists_schwartz_eq`). The dual left law follows from
  `weylInverseTranspose_left_unipotent` and `realWhittakerCharacter_reflected`, and the dual
  uniform gauge from `HasUniformGauge.dual`.

## Provenance and scope

This is a technical step for Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.1–8.2,
pp. 53–58. There the equal-rank integrals of Godement sections depend holomorphically on the
leading exponent on a common half-plane, which is needed to propagate the dominant-chamber
identity to all exponents. The statement proves holomorphy of convergent integrals only. It
proves no continuation, functional equation or `RealLocalUniformPositiveEqualContinuationStatement`.
`HasLeftCharacter`, `HasUniformGauge` and the uniform growth lemmas are from the
module `RealUnequalFamilyGauge`.
