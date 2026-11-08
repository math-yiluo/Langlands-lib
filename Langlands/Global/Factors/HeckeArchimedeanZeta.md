# Archimedean zeta integrals and epsilon factors of actual Hecke characters

Worker 1692 builds this internal archimedean package for the global Hecke
functional equation (package A requested by Worker 1798). It identifies the
Gaussian zeta integrals on the mixed space `V = ℝ^{r₁} × ℂ^{r₂}` with the
archimedean L-factors of the target statement, up to explicit entire
nowhere-vanishing functions, and proves the archimedean local functional
equation that relates them through the target's archimedean epsilon factor.
It uses only the published Library modules `MixedSpaceFourier`
(`Hecke.mixedGaussian`, `Hecke.mixedCharFun`, `Hecke.mixedGaussianConst`,
`Hecke.mixedGaussianFTConst` and the zeta-integral evaluation
`Hecke.integral_mixedGaussian_mul_mixedCharFun`) and the target statement's
definitions of real and complex character presentations.

## Uniqueness of the parameters of inverse characters (namespace `Langlands.LocalFactor.Archimedean`)

- `eq_zero_of_forall_cexp_mul_eq_one`: if `exp(y w) = 1` for every real `y`,
  then `w = 0`. The constant function `y ↦ exp(y w)` has derivative `w` at `0`.
- `ofReal_exp_cpow`: `(e^y : ℂ)^t = exp(y t)` for real `y`.
- `RealCharacterData.parity_eq_and_exponent_eq_neg_of_inv`: if the presented
  real characters satisfy `d'.character x = (d.character x)⁻¹` for all
  `x : ℝˣ`, then `d'.parity = d.parity` and `d'.exponent = -d.exponent`. The
  parity is read off at `x = -1`, where the character is `(-1)^parity`, and the
  exponent from `x = e^y`, where the product of the two characters is
  `exp(y (t' + t)) = 1`.
- `ComplexCharacterData.weight_eq_neg_and_exponent_eq_neg_of_inv`: if
  `d'.character z = (d.character z)⁻¹` for all `z : ℂˣ`, then
  `d'.weight = -d.weight` and `d'.exponent = -d.exponent`. The weight comes from
  `z = e^{iy}`, where the product is `exp(y · i(N' + N)) = 1`, and the exponent
  from `z = e^y`, where it is `exp(y (2u' + 2u)) = 1`.

## Global statements (namespace `Langlands.Global.HeckeFunctionalEquation`)

`realCharacter_inv_of_presentation` and `complexCharacter_inv_of_presentation`:
if `d` presents `χ.infiniteComponent v` and `d'` presents
`χ⁻¹.infiniteComponent v` (the target's `IsRealCharacterPresentation` and
`IsComplexCharacterPresentation`), then `d'.character = (d.character)⁻¹`
pointwise. Every unit of `ℝ` (or `ℂ`) is the image of a unit of the completion
under the fixed ring isomorphism, and the infinite component of `χ⁻¹` is the
inverse of that of `χ` (`HeckeCharacter.infiniteComponent_inv`).

For nonzero additive scales `aR v : ℝˣ`, `aC v : ℂˣ` and presentations `dR`,
`dC` with parities `p_v`, exponents `t_v` (real) and weights `N_w`, exponents
`u_w` (complex), `archimedeanZetaRatio aR aC dR dC s` is

`∏_v |aR v|^(-(s + t_v + p_v)/2) · ∏_w (π/2) ‖aC w‖^(-(s + u_w + |N_w|/2))`,

complex powers of positive reals.
`differentiable_archimedeanZetaRatio` and `archimedeanZetaRatio_ne_zero` show it
is entire and never zero.

`integral_mul_infiniteDenominator`: if `Re(s + t_v + p_v) > 0` and
`Re(s + u_w + |N_w|/2) > 0` at every place, then the integral over `V` of
`mixedGaussian(aR, aC, p, N)(x) · mixedCharFun(p, t, N, u)(x) · N(x)^(s-1)`
(Lebesgue measure, `N` the mixed norm), times the product of the actual
L-factor denominators `(dR v).lFactor.denominator s` and
`(dC w).lFactor.denominator s`, equals `archimedeanZetaRatio aR aC dR dC s`.
The Library evaluates the integral as the product of
`|a|^(-(s+t+p)/2) Γ_ℝ(s + t + p)` and `(π/2) ‖a‖^(-(s+u+|N|/2)) Γ_ℂ(s + u + |N|/2)`.
The denominators are by definition `Γ_ℝ(s + (t + p))⁻¹` and
`Γ_ℂ(s + (u + |N|/2))⁻¹`, and the Gamma factors are nonzero in the right
half-plane.

`mixedGaussianConst_mul_archimedeanZetaRatio_one_sub`: if the dual data satisfy
`p'_v = p_v`, `t'_v = -t_v`, `N'_w = -N_w` and `u'_w = -u_w`, then for every
`s`,

`κ · c_{p,N} · archimedeanZetaRatio aR aC dR' dC' (1 - s)`
`= (∏_v ε_v(s) · ∏_w ε_w(s)) · archimedeanZetaRatio aR aC dR dC s`,

where `κ = mixedGaussianConst` and `c_{p,N} = mixedGaussianFTConst` (for the
real and complex scales and the parities and weights of `dR`, `dC`), and `ε_v`,
`ε_w` are exactly the target's factors
`(dR v).epsilon (aR v) (NNReal.sqrt ‖aR v‖₊) _ s` and
`(dC w).epsilon (aC w) ‖aC w‖₊ _ s`. The proof works place by place. At a real
place, `√|a| · (√|a|)⁻¹ (i·sgn a)^p` cancels to `(i·sgn a)^p`, and the
character value `sgn(a)^p |a|^t` from `character_eq` makes both sides
`(i·sgn a)^p |a|^((s + t - 1 - p)/2)`. At a complex place,
`2‖a‖ · (2‖a‖)⁻¹ i^{|N|} (a/‖a‖)^N` cancels to `i^{|N|} (a/‖a‖)^N`, and with
`χ_w(a) = (a/‖a‖)^N ‖a‖^(2u)` both sides become
`i^{|N|} (a/‖a‖)^N (π/2) ‖a‖^(s + u - 1 - |N|/2)`.

`exists_archimedeanZeta` is the requested package. For an actual Hecke
character `χ`, scales `aR`, `aC`, and presentations `dR`, `dC` of `χ` and
`dR'`, `dC'` of `χ⁻¹` (all retained as hypotheses), it gives `E`, `E'` and
`σ₀` with the following properties:
- `E` and `E'` are entire and nowhere zero;
- for `Re s > σ₀`, the Gaussian zeta integral of `χV = mixedCharFun` (built
  from `dR`, `dC`) against `F = mixedGaussian(aR, aC, p, N)`, times the target's
  `infiniteDenominator s`, is `E s`;
- for `Re s > σ₀`, the zeta integral of `χV'` (built from `dR'`, `dC'`) against
  `G = mixedGaussian(aR, aC, p, -N)`, times the target's
  `dualInfiniteDenominator s`, is `E' s`;
- for all `s`, `κ · c_{p,N} · E'(1 - s) = infiniteEpsilon(s) · E(s)`.

Here `E` and `E'` are `archimedeanZetaRatio` for the original and dual data,
and `σ₀` is the sum of the norms of all exponents. The parameter relations come
from the uniqueness lemmas applied to the presentation equations. With
`p' = p` and `N' = -N`, the dual integral has the form of the Library
evaluation for the data `dR'`, `dC'`.

This module does not prove Poisson summation, the identification of the
Fourier transform of `F` with `c_{p,N} G` in the global argument (supplied by
`Hecke.fourierIntegral_mixedGaussian`), unit-cone integrals, the finite places
or the global functional equation.
