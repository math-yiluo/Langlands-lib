# Rapid determinant weights on the ordinary real gap kernel

This module is the real counterpart of the Library's `ComplexGapOrdinaryWeighted`; its declarations lie in
`Langlands.Global.RankinSelbergGlobal.RealGapOrdinaryWeighted`.

`HasSplitPartialTest h a F f Φ₀ Ξ Ψ` says that a square test `F` on `(r+1) × (r+1)` matrices is the product
`Φ₀(leading columns) · Ξ(trailing columns)` on every invertible matrix and that the positive Fourier
transform `realFourierTransform a f` of the last-column test equals the Schwartz function `Ψ`.

`weightedBlockKernel` is the ordinary block kernel after the quotient change of variables, with one radial
weight `f₁` on the quotient determinant (inside `weightedOrdinary`) and one weight `f₂` on the determinant
of the leading block. `coupledWeightedBlockKernel` evaluates the two weights at the quotient determinant
divided by the retained determinant and at the leading determinant multiplied by it, with the Mellin
shift of the smaller zeta integral. `coupledHaarKernel` is the same kernel before the right-tail chart:
the padded Godement integrand on the quotient, the lower rectangle and the ambient group `GL_(r+1)(ℝ)`,
and `coupledHaarKernel_eq` reads it as `paddedRestrictionKernel` at the representative of the quotient.

* `realGapCoupledPowerBounds`: for `W` in `realUniformWhittakerModel r ds (−a)`, `V` in
  `realUniformWhittakerModel t es a`, a character `c` and a split test, there are thresholds `α₀`, `γ₀`
  such that `coupledWeightedBlockKernel` is integrable for the quotient measure, the lower rectangle and
  `rightTailProductMeasure` whenever the profiles `f₁`, `f₂ : ℝ → ℂ` are measurable and satisfy
  `‖f₁ x‖ ≤ C₁ x^α` and `‖f₂ x‖ ≤ C₂ x^γ` for every `x > 0`, with `α ≥ α₀` and `γ ≥ γ₀`.
* `realGapCoupledHaarPowerBounds` gives the same, under the same hypotheses on measurable `f₁`, `f₂`, for
  `coupledHaarKernel` against an arbitrary Haar measure `μH` on `GL_(r+1)(ℝ)` (with `κ` an
  inversion-invariant Haar measure on the orthogonal group), and
  `RealGapCoupledHaarStatement`, proved by `realGapCoupledHaar`, specializes to rapidly decaying
  measurable profiles.

## Proof

The block-column identities give the inputs of `Φ₀`, `Ξ`, `Ψ`; the translated Whittaker product is
continuous by descent to the quotient, so the coefficient part of the kernel (everything except the two
profiles) is continuous, hence measurable. The profiles enter through `f₁` and `f₂` composed with
continuous functions of the absolute determinants, so the measurability of `f₁` and `f₂` makes the full
kernel measurable; this is where the measurability hypotheses are used. The norm of the character and of
the determinant power are real powers of the absolute determinant (`norm_detCharacter`,
`norm_detPower`). Each profile bound is a power of its determinant argument, and the extra powers of the
retained determinant enter the arbitrary determinant exponent of `realGapOrdinaryConvergence`, with the
right-tail density moved into the integrand. For the Haar form, the right quotient shear by the leading
block (`measurePreserving_quotientShift`, with `blockUnfoldedKernel_shift` at the representatives) pulls
`coupledHaarKernel` back to the coupled kernel on the right-tail coordinates, and the right-tail Haar
formula `realTwoBlockRightHaar` writes `μH` as a positive multiple of the image of the right-tail measure.

These are the convergence statements used before the complementary rectangle integration in the
rigorous version of the larger-gap recurrence, Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§10.4, Lemmas 10.5–10.7, pp. 77–81.
