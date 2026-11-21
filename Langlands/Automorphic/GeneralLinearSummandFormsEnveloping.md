# Enveloping differentiation in a closed invariant subspace of the quotient L²

`GeneralLinearClosedFormClassesEnvelopingStatement` uses the canonical
positive-central quotient of `GL_{r+1}` with the same split-centre data and
right-invariance hypothesis as
[the summand realization statement](GeneralLinearCuspidalSummandRealizationStatement.md).
The additive adelic quotient of the number field is assumed compact. Let `A`
be a closed complex submodule of the quotient `L²`, invariant under the
genuine adelic right action. If a stable automorphic function `f` represents
a class `φ ∈ A` in the sense of `IsGeneralLinearFormClass`, then for every
archimedean enveloping-algebra element `D`, the genuine differential `D f`
represents some class in `A`. This class claim does not require `f` to be
cuspidal. `generalLinearClosedFormClassesEnveloping` proves it.

`generalLinearSummandFormsEnveloping` proves the exact
`GeneralLinearSummandFormsEnvelopingStatement` in the
[summand realization reduction](GeneralLinearCuspidalSummandRealizationReduction.md).
For each closed invariant `P` of the full almost-everywhere cuspidal space
`S`, the attached stable, pointwise cuspidal forms with classes in `P` are
invariant under the enveloping action.

## Implemented proof

Use the top operator realization and the published
`OperatorRealization.exists_reproducingKernel` in
[CuspidalAdmissible/Reproduction](CuspidalAdmissible/Reproduction.md). The
stable vector `f` is reproduced by one smooth compactly supported kernel `κ`
at every adelic point `x`. At `x`, the smooth function of the archimedean
variable `g` with value `f(x g)` is the left translate by `x`'s archimedean
coordinate of the smooth slice at its finite coordinate. Its convolution
with `κ` is the same smooth function by the reproduction identity. By
[`compactKernelConvolutionDifferentiation`](../Global/ArchimedeanConvolutionDifferentiationProof.md),
differentiation transfers to the kernel. Evaluating the derivative at `1`
and using covariance under left translation and the slice formula for the
concrete operator gives

\[
(D f)(x) = \int_{G_\infty} f(x z)\,(D\kappa)(z^{-1})\,d z
\]

for the chosen left Haar measure and the actual inclusion of `G_∞`.

The weight `w(z) = (Dκ)(z⁻¹)` is continuous and compactly supported by
`envelopingCompactSupport` and the inversion homeomorphism. Apply
[the weighted orbit comparison](GroupSchemeQuotientL2IntegratedRepresentative.md)
to the continuous representative of `φ` and the inclusion of `G_∞`, via
the matrix-to-group-scheme homeomorphism. It gives an integrable family
`w(z) • ρ(z) φ` and identifies its Bochner integral with the class of the
continuous pointwise integral. Each integrand lies in `A`. The continuous
linear map to the quotient by the closed submodule `A` commutes with the
Bochner integral, and annihilates every integrand, so the integral belongs
to `A`. Pulling the continuous representative back to adelic points and
using the pointwise identity above identifies it with `D f`.

For the cuspidal specialization, take `A = P.map S.subtype`. The inclusion
of `S` is a closed embedding and intertwines the right actions, so `A` is
closed and invariant. The existing `generalLinearCuspidal_envelopingAction`
applied to `adelicConstantTermEnveloping` preserves the matrix-model cusp
condition. Together these facts prove differential stability for the
attached forms.

## Provenance and scope

This is a derived step for the summand-to-realization direction of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Theorem 9.7.3,
pp. 265–266 (PDF pp. 277–278), in particular the comparison in (9.40). The
implemented argument uses compact reproduction for a form that already has
an `L²` class; it does not assume or prove the rapid-decay assertion of
Theorem 9.7.1, p. 264 (PDF p. 276). It does not show that any nonzero class in
an arbitrary irreducible summand comes from a stable form, nor does it prove
algebraic irreducibility of the attached forms.
