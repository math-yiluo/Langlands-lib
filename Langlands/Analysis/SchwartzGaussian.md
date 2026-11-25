# The radial Gaussian as a Schwartz function

The module `Langlands.Analysis.SchwartzGaussian` declares

```text
def Langlands.Global.RankinSelbergGlobal.ComplexGodementGaussianPolynomial.radialGaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] : 𝓢(E, ℝ)
```

the function `x ↦ exp (-‖x‖²)` on a real inner product space, as a real Schwartz function.
The name is the one under which the Gaussian polynomial tests of
[ComplexGodementGaussianPolynomial](../Global/RankinSelberg/ComplexGodementGaussianPolynomial.md)
use it; that module and
[RealGodementGaussianPolynomial](../Global/RankinSelberg/RealGodementGaussianPolynomial.md)
import this one. The file depends on Mathlib only, so that the Gaussian can be used without the
global Rankin–Selberg and Hecke theory (the real Weil representation uses it for its Gaussian
vector, `Langlands.Theta.gaussianVector`).

## Content

Smoothness: `x ↦ -‖x‖²` has temperate growth, and `exp` is smooth. Decay: the first `n`
derivatives of `Q(x) = -‖x‖²` are bounded uniformly by a polynomial in `1 + ‖x‖`; all
derivatives of `exp` are `exp`, so the bound for iterated derivatives of a composition gives
`‖D^n (exp ∘ Q)(x)‖ ≤ n! · exp(Q x) · (A (1 + ‖x‖)^l)^n`, and the Gaussian decay
estimate `exp(-u²) ≤ B (1 + u)^{-r}` absorbs every power of `1 + ‖x‖`.

The two estimates used (`r^k e^{-b r²} ≤ C e^{-b r²/2}` and `e^{-c u²} ≤ C (1 + u)^{-r}`) are
private lemmas of this file. They are the lemmas `exists_pow_mul_exp_neg_le` and
`exists_exp_neg_mul_sq_le_rpow` of `Langlands.Global.Hecke` (in
`Langlands/Global/Hecke/MixedSpaceFourier.lean`), restated here because that file imports the
Hecke theory.

## Declarations

- `radialGaussian` (definition).

## Dependencies

Mathlib: `Analysis.Distribution.SchwartzSpace.Basic`, `Analysis.SpecialFunctions.ExpDeriv`,
`Analysis.SpecialFunctions.Pow.Real`, `Analysis.Calculus.ContDiff.Bounds`,
`Analysis.InnerProductSpace.Calculus`, `Analysis.Complex.Exponential`.
