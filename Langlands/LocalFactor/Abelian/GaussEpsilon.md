# Elementary laws of the concrete Gauss epsilon expression

Worker 1248. Internal lemmas about the published expressions
`PadicAbelian.epsilonAt` and `PadicAbelian.lFactorAt` at explicit conductor levels
`a` (multiplicative) and `n` (additive). They are derived directly from the
definitions in `Langlands.LocalFactor.Abelian.Padic` and from scalar additive
Haar scaling; they are the elementary laws of Tate's local epsilon factor
(Tate's thesis, local theory).

* `epsilonAt_eq_zero_mul`, `epsilonAt_eq_half_mul`: on the shell of order
  `-(n+a)` the integrand's spectral factor is `q^(-(n+a)s)` (Lean
  `gaussIntegrand_on_shell_spectral`), so `ε(s) = ε(0) q^(-(n+a)s)` and
  `ε(s) = ε(1/2) q^(-(n+a)(s-1/2))`. The unramified branch is checked directly.
  `epsilonAt_differentiable` follows.
* `chi_eq_zpow_ord`: for conductor `0`, `χ(b) = χ(π)^(ord b)`. Hence the Euler
  factor and the unramified epsilon expression do not depend on the uniformizer
  (`lFactorAt_uniformizer_eq`, `epsilonAt_uniformizer_eq`); the ramified
  expression does not involve the uniformizer at all.
* `epsilonAt_eq_shell`: for `c` of order `n + a`, the shell is `c⁻¹ O^×`
  (`image_mul_integralUnits`), giving the `c`-shell formula; in the unramified
  case `χ(c) |c|^(s-1) μ(O)` equals the defining expression.
* `epsilonAt_smul_measure`: scaling the Haar measure by `r > 0` scales `ε` by `r`.
* `epsilonAt_mulShift`: replacing `ψ` by `x ↦ ψ(bx)` moves the conductor to
  `n + ord b`; the substitution `x ↦ bx` (`preimage_mul_gaussShell`, scalar Haar
  scaling) gives the factor `χ(b) |b|^(s-1)`.
* Unramified twists `ω` (conductor `0`): `characterExtension_mul_unramified`,
  `epsilonAt_mul_unramified` (factor `ω(π)^(n+a)`), `lFactorAt_mul_unramified`
  and `epsilonAt_mul_unramified_shift` (if `ω(π) = q^(-t)`, both expressions shift
  `s` by `t`), using `spectralVariable_mul`.

`characterExtension_unit_mul` is the multiplicativity `χ(bx) = χ(b) χ(x)` of the
zero-extended character.
