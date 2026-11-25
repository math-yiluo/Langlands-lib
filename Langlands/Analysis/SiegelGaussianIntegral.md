# Gaussian integrals over the Siegel upper half space

The module `Langlands.Analysis.SiegelGaussianIntegral` evaluates the Gaussian integrals
`∫ e^{πi xᵀ σ x + 2πi wᵀ x} dx` over `ℝ^ι` for `σ` in the Siegel upper half space.

## Content

`siegelGaussianIntegral σ = ∫ e^{πi xᵀ σ x} dx`. For Siegel `σ`:

- `∫ e^{πi xᵀ σ x + 2πi wᵀ x} dx = siegelGaussianIntegral σ · e^{-πi wᵀ σ⁻¹ w}`
  (`Matrix.IsSiegel.integral_cexp_quadratic`);
- `siegelGaussianIntegral σ ² · det (-iσ) = 1` (`Matrix.IsSiegel.siegelGaussianIntegral_sq_mul_det`),
  in particular the integral does not vanish.

Write `σ = Pᵀ (diagonal t) P` (`Theta`-independent diagonalization of
`Langlands/LinearAlgebra/SiegelUpperHalfSpace`), change variables by `P`
(`integral_comp_mulVec_of_det_ne_zero`), and apply Mathlib's one-dimensional complex Gaussian integral
in each coordinate. Consequence: `(∫ c e^{πi xᵀ τ x} · e^{-π xᵀ x} dx)² · det (1 - iτ) = c²`
(`siegelGaussian_pair_standardGaussian`), the pairing of a Siegel Gaussian with the standard one,
used for the vacuum matrix coefficient of the Weil representation. G. B. Folland, *Harmonic
analysis in phase space* (1989), Appendix A, Theorem 1, p. 256 (proof pp. 256–257): for `A = Aᵀ`
with `Re A` positive definite, `∫ e^{-πx·Ax - 2πiz·x} dx = (det^{-1/2} A) e^{-πz·A⁻¹z}`; here
`A = -iσ`. Folland also fixes the branch of `det^{-1/2} A`; the Library proves only
`siegelGaussianIntegral σ ² · det (-iσ) = 1`, not which square root the integral is.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean`, lines 117–196
(`siegelGaussIntegral`, `integral_comp_mulVec_of_det_ne_zero`, `IsSiegel.exists_integral_cexp_quadratic`,
`IsSiegel.integral_cexp_quadratic`, `IsSiegel.siegelGaussIntegral_sq_mul_det`,
`IsSiegel.siegelGaussIntegral_ne_zero`), and `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelGaussianPairStandardGaussian.lean` (whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory` → `Langlands`; `siegelGaussIntegral` → `siegelGaussianIntegral` (and in the
  lemma names); `siegelGauss_pair_standard` → `siegelGaussian_pair_standardGaussian`.
- Lines 198–334 of the source file (Poisson summation, the transformation law of Riemann theta
  functions) are not taken.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- def `Langlands.siegelGaussianIntegral`
- theorem `Langlands.integral_comp_mulVec_of_det_ne_zero`
- theorem `Langlands.Matrix.IsSiegel.exists_integral_cexp_quadratic`
- theorem `Langlands.Matrix.IsSiegel.integral_cexp_quadratic`
- theorem `Langlands.Matrix.IsSiegel.siegelGaussianIntegral_sq_mul_det`
- theorem `Langlands.Matrix.IsSiegel.siegelGaussianIntegral_ne_zero`
- theorem `Langlands.siegelGaussian_pair_standardGaussian`

## Dependencies

`Langlands.LinearAlgebra.SiegelUpperHalfSpace`; Mathlib (`Analysis.SpecialFunctions.Gaussian.FourierTransform`,
`MeasureTheory.Function.Jacobian`).
