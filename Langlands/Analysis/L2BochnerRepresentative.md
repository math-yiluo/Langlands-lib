# Representatives of Bochner integrals in complex L²

`Langlands.Analysis.coeFn_integral_l2_ae_eq` compares an integral in `Lp ℂ 2 μ`
with a scalar integral. Let `μ` be σ-finite on `X` and `ν` be s-finite on `Y`.
Suppose `A : Y → Lp ℂ 2 μ` is Bochner integrable for `ν` and `f : Y × X → ℂ`
is almost everywhere strongly measurable for `ν.prod μ`. If for `ν`-almost
every `y` the fibre `f(y, ·)` represents the class `A y`, then `x ↦ ∫ y,
f(y, x) ∂ν` represents the Bochner integral `∫ y, A y ∂ν`. The assertion is
about `μ`-almost everywhere equality, not equality for all choices of values
of the representatives at every point.

## Implemented proof and provenance

This is a derived Fubini lemma, used by the [quotient orbit comparison](../Automorphic/GroupSchemeQuotientL2IntegratedRepresentative.md).
For any measurable set `s ⊆ X` of finite `μ`-measure, multiplication by its
indicator maps `L²(μ)` continuously linearly into `L¹(μ)` by Hölder's inequality.
Composing with the integral on `L¹(μ)` gives the continuous linear functional
of integrating a class over `s`. The `L¹` norm of the indicator-multiplied
class is the integral of its absolute value over `s`. Applied to the family
`A`, this proves product integrability of `f` for `ν.prod (μ.restrict s)`
using the fibre identification and Mathlib's `integrable_prod_iff`.
Commuting the functional with the Bochner integral and then using Fubini gives
equality of the two integrals over `s`. Mathlib's
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` turns those tests into the
claimed almost everywhere equality. The proof does not require global
`L¹(μ)` integrability of the `L²` classes.
