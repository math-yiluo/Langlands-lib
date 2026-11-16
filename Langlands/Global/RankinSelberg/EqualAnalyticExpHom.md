# Continuous exponential functions on the real line

Module `Langlands.Global.RankinSelberg.EqualAnalyticExpHom`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

`exists_eq_cexp_of_continuous`: let `f : ℝ → ℂ` be continuous with `f 0 = 1` and
`f (x + y) = f x * f y`. Then there is `w : ℂ` with `f x = exp (w x)` for all `x`.

## Proof

Continuity at `0` gives `δ > 0` with `c = ∫₀^δ f ≠ 0`. The functional equation gives
`f(x) c = ∫ₓ^(x+δ) f = G(x + δ) - G(x)`, where `G(u) = ∫₀^u f` has derivative `f`
(fundamental theorem of calculus). So `f` is differentiable with
`f' = (f(x + δ) - f(x))/c = w f(x)`, where `w = (f(δ) - 1)/c`. Hence `f(x) exp (-w x)` has
derivative zero. By `is_const_of_deriv_eq_zero` it is constant, equal to its value `1` at `0`.

## Provenance

Classical. The proof is internal and uses only Mathlib. In this development the lemma
classifies idele class characters that are trivial on norm-one ideles
(`EqualAnalyticIdeleCharacter`).
