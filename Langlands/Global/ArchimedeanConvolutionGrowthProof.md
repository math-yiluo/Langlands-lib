# Polynomial bounds for compact-kernel right convolution

This unit proves the published
`Langlands.Global.ArchimedeanGL.CompactKernelConvolutionBoundStatement K n`
with theorem `Langlands.Global.ArchimedeanGL.compactKernelConvolutionBound`.
It imports the unchanged
[`ArchimedeanConvolutionGrowthStatement`](ArchimedeanConvolutionGrowthStatement.md)
and preserves its whole quantified proposition without additional hypotheses.
Both the theorem and its polynomial-growth corollary are polymorphic in
`K : Type u` with `[Field K] [NumberField K]` and in every `n : ℕ`, including
zero.

## Quantifiers and convention

The bound holds for every Borel-compatible measurable structure on the actual
`InfiniteAdelicGL K n`, every left-invariant measure `μ` finite on compact sets,
continuous complex functions `f` and `κ` with `HasCompactSupport κ`, and every
real `C ≥ 0` and natural `d` satisfying
`‖f(g)‖ ≤ C * matrixHeight K n g ^ d`. It produces `D ≥ 0` such that

```text
‖∫ y, f(y) * κ(y⁻¹ * g) dμ(y)‖ ≤ D * matrixHeight K n g ^ d
```

for every `g`. The exponent is unchanged. The measure need not be nonzero or
normalized, so the result includes the zero measure. No positive-rank instance
is used, and the empty-matrix case follows by the same proof.

## Implemented proof

For the supplied `C` and `d`, define the real weight
`w(z) = ‖κ(z⁻¹)‖ * matrixHeight K n z ^ d`. Continuity follows from continuity
of inversion, the kernel, the norm, and the published matrix height. Pullback
by the inversion homeomorphism preserves compact support, as do taking the
norm and multiplication by the height factor. Therefore
`Continuous.integrable_of_hasCompactSupport` proves integrability of `w`
for `μ`. The weight is nonnegative, so the proposed constant
`D = C * ∫ z, w(z) dμ(z)` is nonnegative.

`integral_mul_left_eq_self` changes variables by `y = g * z`. The group identity
`(g * z)⁻¹ * g = z⁻¹` transforms the convolution into
`∫ z, f(g * z) * κ(z⁻¹) dμ(z)`. The input estimate,
`matrixHeight_mul_le`, monotonicity of natural powers on nonnegative reals,
and `mul_pow` bound its integrand norm by
`(C * matrixHeight K n g ^ d) * w(z)`.

The majorant is integrable by `Integrable.const_mul`.
`norm_integral_le_of_norm_le` bounds the norm of the Bochner integral by its
integral, and `integral_const_mul` gives the stated bound after rearranging
real multiplication. This Mathlib comparison theorem requires integrability
of the majorant only; it is formulated for the total Bochner integral.
Accordingly, this implementation retains but does not use continuity of `f`,
and does not separately establish an integrability theorem for the convolution
integrand.

The corollary `Langlands.Global.ArchimedeanGL.compactKernelConvolutionGrowth`
proves `CompactKernelConvolutionGrowthStatement K n` by applying the published
logical implication `compactKernelConvolutionGrowth_of_bound` to the bound
just proved.

## Provenance and scope

The implemented proof was supplied by Worker 94 in the shared parent task draft
and checked and documented for this proof submission by Worker 347. It is an
internal analytic consequence of the Library's actual matrix/inverse height
lemmas and Mathlib's integration theorems. The statement's companion Markdown
records the original automorphic motivation; this proof makes no new claim of
correspondence with a numbered literature theorem.

This is the elementary compact-kernel convolution estimate. Existence of a
smooth reproducing kernel, transfer of genuine enveloping differentiation
under the integral, and the final automorphic differential-growth theorem
remain separate obligations. This proof assumes none of them and does not
construct a Haar measure or a smooth-kernel space.
