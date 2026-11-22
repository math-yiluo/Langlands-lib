# The real finite normalized traces on common convergence chambers

This module is the real counterpart of the published complex module
`ComplexLocalEqualFiniteSquareChambers`. It upgrades `RealLocalEqualFiniteSquareNormalized`,
whose trace identities hold on chambers that may depend on the square test, to identities on
two chambers chosen before the test. Notation: `m = t + 1`, `n = t + 2`, `D` and `D'` real
quotient data of ranks `t` and `t + 1`, and `equalUnfoldedKernel` the kernel of Jacquet's
unfolded integral (8.1) from `RealLocalEqualUnfolding`.

## Lemma

`exists_uniformModel_equalKernel_chamber`: let `W` lie in the uniform real Whittaker model of
rank `m` for some block list and character `a`, and `V` in the uniform model of rank `n` with
character `-a`. Then there are `τ, σ` such that `equalUnfoldedKernel (charData e z) Ψ W V s` is
integrable for `D.measure × D'.groupHaar` for every parity `e`, every square Schwartz test `Ψ`
and all `z, s` with `τ < Re z` and `σ < Re s`.

Proof: the Library's `realUniformWhittakerRegularity` gives regularity and moderate growth.
`RealWhittakerGauge.exists_gauge_bound` gives the gauge estimates. The left unipotent character
has modulus one (`RealUnequalPairConvergence.norm_realWhittakerCharacter`), so `|V|` is left
`U`-invariant. Then `realLocalEqualJointIntegrability` applies with `x₀ = Re z ≥ ρ` and
`y₀ = Re s > σ`. The exponent of `charData e z` is `z`.

## Definition

`RealMatrixCoefficientNormalizedGrowth t D' a e es f Ψ us vs usd vsd bM cM hcM signM` is
literally the matrix hypothesis of `RealLocalEqualFiniteSquareNormalizedStatement` for the
square test `Ψ`. It covers every linear form `ℓ` on the smooth position principal series of
`expand es` with a compact derivative bound, and the matrix coefficient
`b_ℓ = realStandardMatrixCoefficient es ℓ f`:

* the integrand `Ψ(g) sgn(det g)^e |det g|^(w + m/2) b_ℓ(g)` is `D'.groupHaar`-integrable on a
  right half-plane in `w`;
* so is the corresponding integrand with the Fourier test
  `realRectangularSchwartzFourier (-a) Ψ` and `b_ℓ ∘ (inverse transpose)`;
* the two integrals `realWeightedMatrixIntegral` satisfy `HasRealPairNormalizedGrowth` with
  lists `us, vs, usd, vsd`, epsilon data `bM, cM` and sign `signM`.

## Statement

`RealLocalEqualFiniteSquareChambersStatement t` has the hypotheses of
`RealLocalEqualFiniteSquareNormalizedStatement` that do not involve the square test:

* character lists `cs, fs` of lengths `m, n`;
* `W` in the uniform model for `cs` and `a`;
* a uniform Whittaker map `B` for `fs` and `-a` with a continuous Whittaker evaluation, and a
  standard vector `f`;
* the normalized corank-one equation for every coefficient of the larger model paired with
  `W`, with arbitrary lists `xs, ys, xsd, ysd`, epsilon data `bA, cA` and sign `signA`;
* arbitrary matrix data `us, vs, usd, vsd, bM, cM, signM`.

It asserts thresholds `τ, σ, τ_d, σ_d` with three properties:

1. For every square Schwartz test `Ψ` and `τ < Re z`, `σ < Re s`, the primal kernel
   `equalUnfoldedKernel (charData e z) Ψ W (B f) s` is integrable.
2. For every `Ψ` and `τ_d < Re(-z)`, `σ_d < Re s`, the dual kernel
   `equalUnfoldedKernel (charData e (-z)) Ψ W̃ (B f)~ s` is integrable. Here `~` is the Weyl
   inverse-transpose dual `ArchimedeanLocal.dualFunction`.
3. For every `Ψ` with finite-dimensional left orthogonal span that satisfies
   `RealMatrixCoefficientNormalizedGrowth`, there are entire functions `F` and `Fd` on `ℂ²`,
   each with strip growth in `s` for fixed `z` and along `z = v + s`. They satisfy:
   * on the primal chamber,
     `F(z, s) = den(xs, ys)(s) · den(us, vs)(s + z) · ∫ equalUnfoldedKernel (charData e z) Ψ W (B f) s`;
   * on the dual chamber, with the Fourier test `Ψ̂ = realRectangularSchwartzFourier (-a) Ψ`,
     `Fd(z, s) = den(xsd, ysd)(s) · den(usd, vsd)(s - z) · ∫ equalUnfoldedKernel (charData e (-z)) Ψ̂ W̃ (B f)~ s`;
   * for all `z, s`,
     `Fd(z, 1 - s) = signA · ε(xs, ys)(s) · signM · ε(us, vs)(s + z) · F(z, s)`.

## Proof

The two chambers come from `exists_uniformModel_equalKernel_chamber`, which needs coefficients
with opposite characters. The primal chamber uses `W` with character `a` and `B f` with
character `-a`. The dual chamber uses the duals: `W̃` with character `-a` and `(B f)~` with
character `a`. Their memberships come from the Library's `realUniformWhittakerCharacterDual`
for the character lists `dualCharacterBlocks cs` and `dualCharacterBlocks fs`. For a given test,
`realLocalEqualFiniteSquareNormalized` gives `F`, `Fd`, the growth, the reflection identity,
and the two trace identities on test-dependent deep chambers. These identities extend to the
common chambers by `eq_mul_integral_equalUnfoldedKernel_of_deep` (from
`RealLocalEqualChamberTrace`). That lemma is an identity-theorem argument: along lines with
fixed `s` and with fixed `z`, both sides are holomorphic on the half-planes of absolute
convergence. The primal multiplier `N(z, s) = den(xs, ys)(s) den(us, vs)(s + z)` is entire,
since reciprocal `L`-factors are entire (`ReciprocalEntire.entire`). On the dual side the lemma
is applied to `Gd(z, s) = Fd(-z, s)` with the multiplier
`Nd(z, s) = den(xsd, ysd)(s) den(usd, vsd)(s + z)`. Then `z` is replaced by `-z`.

## Provenance and scope

This is an internal step for Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.2,
pp. 55–58.

On p. 55 Jacquet claims that the unfolded integral (8.1) converges absolutely for `Re s` large,
uniformly for the inducing exponents in any relatively compact set, and he uses this claim on
p. 56. The claim fails in that generality. In rank two, with trivial exponents, Gaussian tests
and a nonzero Whittaker function, the absolute integral diverges for every `s`. The divergence
comes from the unipotent variable, where an integral of `(y₁² + u² y₂²)^(-1/2)` in `u` appears;
see the example in `RealLocalEqualJointIntegrability.md`. The example shows failure outside the
dominant range for that test. For particular tests, convergence may still hold at such
exponents. The real joint integrability theorem gives sufficient thresholds, valid for every
square Schwartz test at once, once the separated leading exponent dominates. The Lean chambers
therefore carry two thresholds each:

* the primal chamber needs `τ < Re z` and `σ < Re s`;
* the dual chamber needs `τ_d < Re(-z)` and `σ_d < Re s`.

Both chambers are fixed before the test, from the real joint integrability theorem. The
identity-theorem lemma of `RealLocalEqualChamberTrace` moves the trace identities from the
test-dependent deep chambers to these product chambers, where absolute convergence is
established. This follows the published complex module `ComplexLocalEqualFiniteSquareChambers`.

On pp. 56–58 Jacquet treats `K_n`-finite square tests through a compact idempotent, the finite
product formula (8.2) and its reflected counterpart. The finite normalization formalized in
`RealLocalEqualFiniteSquareNormalized` corresponds to this step. The later passage to all
square tests, in `RealLocalEqualSquareLimit`, is an internal step and not part of Jacquet's
text. Like the module it builds on,
the statement keeps three inputs explicit: the continuous Whittaker evaluation, the corank-one
equation and the matrix equation. It proves no continuation for non-finite tests or for the
actual equal-rank integral, and it does not prove `RealLocalUniformPositiveEqualContinuationStatement`.
