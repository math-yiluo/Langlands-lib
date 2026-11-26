# Same-field equal-rank Whittaker integration

Module `Langlands.Global.RankinSelberg.EqualFactorizationAtReductionProof`, namespace
`Langlands.Global.RankinSelbergGlobal`. The theorem
`equalArchimedeanFactorizationAtReduction` proves
`EqualArchimedeanFactorizationAtReductionStatement.{u,uQ}` of
[`EqualFactorizationAtStatement`](EqualFactorizationAtStatement.md), with both universe
parameters free. For every number field `F : Type u` with compact `AdeleQuotient F`, it
derives `EqualArchimedeanFactorizationAt F` from `EqualPointwiseFactorizationAt F`. The only
other inputs are theorems of the Library. The module imports the statement module and
[`UnipotentClassProductProof`](UnipotentClassProductProof.md) and changes neither.

## Inputs at the field `F`

The proof first introduces `F`, its instances and the pointwise hypothesis at `F`. Then it
introduces every binder of `EqualArchimedeanFactorizationAt F`: the additive character `ψ`,
the rank `r`, the realizations and presentations, the finite set `S`, and the additive and
archimedean parameters. These binders are identical to those of
`EqualPointwiseFactorizationAt F`, so the hypothesis is applied once, at the same `F` and to
the same arguments. No pointwise statement at another field is used, and total complexity
of `F` is not needed.

The hypothesis supplies vectors `x`, `x'` and a Schwartz–Bruhat function `Φ`. It also gives
a scalar `κ ≠ 0`, archimedean Whittaker restrictions `WR`, `WR'`, `WC`, `WC'`, archimedean
Schwartz functions `ΦR`, `ΦC` and quotient measure data `DR`, `DC`. At each `v : S` it gives
local test data `D v` and functions `fS v s`, `gS v s` on the local quotient. Together with
these come all the clauses of the pointwise body, among them the two pointwise identities.

The theorem `UnipotentClass.unipotentClassProductStatement` is then applied at the same `F`,
with `t = r`, the same `S` and the data `DR`, `DC`. At each `v : S` the finite measure is
`equalPadicQuotientMeasure (padicField v) r`, compatible by
`equalPadicQuotientMeasure_isCompatible`. The theorem gives one constant `CB ≠ 0`. For every
family of local functions on the quotients `N_(r+1) \ GL_(r+1)`, the integral of their
product over `unipotentIntegralClasses F (r + 1) S`, against `whittakerQuotientMeasure`, is
`CB` times the product of the local quotient integrals. The constant is fixed before the
local functions are chosen, so both integrations below use the same `CB`.

## Integrating the ordinary identity

The witnesses for the integrated body are the same `x`, `x'`, `Φ`, `WR`, `WR'`, `ΦR`, `DR`,
`WC`, `WC'`, `ΦC`, `DC` and `D`, with `c = CB * κ` and `σ = 0`. The scalar `c` is nonzero by
`mul_ne_zero`. Fix `s`, write `W` and `W'` for the global cusp Whittaker functions of `x`
and `x'`, and argue as follows.

1. `partialEqualWhittakerIntegral_eq_setIntegral` rewrites
   `partialEqualWhittakerIntegral F S W W' Φ s` as the integral of
   `equalWhittakerIntegrand F W W' Φ s` over the measurable set
   `unipotentIntegralClasses F (r + 1) S` (`measurableSet_unipotentIntegralClasses`).
2. On that set the ordinary pointwise identity equates the integrand with `κ` times a
   product. Its factors are `realEqualIntegrand (WR v) (WR' v) (ΦR v) s` at
   `realQuotientProjection F r v q` for the real places, and the corresponding
   `complexEqualIntegrand` factors for the complex places. At the places of `S` they are
   the values `fS v s` at `finiteQuotientProjection F r v q`. `setIntegral_congr_fun`
   substitutes this product into the integral, and `integral_const_mul` takes out `κ`.
3. The quotient-product formula, applied to these local functions, turns the remaining
   integral into `CB` times three factors. These are the real-place and complex-place
   integrals against `(DR v).measure` and `(DC w).measure`, and the integrals of `fS v s`
   against `equalPadicQuotientMeasure`.
4. The pointwise hypothesis identifies the integral of `fS v s` with `(D v).integral s`.
   Unfolding `realEqualIntegral`, `complexEqualIntegral` and `equalIntegral` identifies the
   archimedean integrals with the factors of `infiniteIntegral s`.
5. `ring` regroups the product as `c * infiniteIntegral s * ∏ v : S, (D v).integral s`.

## Integrating the dual identity

The dual identity is integrated in the same way, with the dual pointwise identity in step 2.
The integrand is `equalWhittakerIntegrand F Wdual W'dual Φhat s`, for the global dual
functions of `W` and `W'` and the global Fourier transform `Φhat` of `Φ`. On the integral
classes it equals `κ` times a product of local factors. At the infinite places these are
the equal-rank integrands of `ArchimedeanLocal.dualFunction (r + 1)` of the local Whittaker
functions, with the local Fourier transforms `realFourierTransform (aR v) (ΦR v)` and
`complexFourierTransform (aC w) (ΦC w)`. At the places of `S` they are the values of
`gS v s`. The same constant `CB` is used, and the pointwise hypothesis identifies the
integral of `gS v s` with `(D v).dualIntegral s`. Unfolding `realEqualDualIntegral`,
`complexEqualDualIntegral` and `equalIntegral` identifies the archimedean factors with
those of `infiniteDualIntegral s`. The result is
`c * infiniteDualIntegral s * ∏ v : S, (D v).dualIntegral s`, with the same `c = CB * κ` as
for the ordinary identity, since both pointwise identities carry the same `κ`.

Both identities are proved for every complex `s`, so they hold in particular on the
half-plane `0 < s.re` required with `σ = 0`. No integrability or convergence hypothesis is
used: the quotient-product theorem holds for every family of local functions, and the
pointwise identities hold at every class of the integration set.

## Why the remaining clauses carry over

The other clauses of `EqualArchimedeanFactorizationAt F` occur word for word in
`EqualPointwiseFactorizationAt F`. They are about the same witnesses, which the proof
passes on unchanged, so it reuses the hypotheses as they are.

- Whittaker restrictions. The four clauses `IsRealPlaceWhittaker` and
  `IsComplexPlaceWhittaker` concern `WR`, `WR'`, `WC` and `WC'` only.
- Schwartz–Bruhat data. Sphericity of `x` and `x'` outside `S`, membership of `Φ` in
  `schwartzBruhat F (r + 1)` and standardness of `Φ` outside `S` concern only these
  vectors and `Φ`.
- Product formulas. The Schwartz–Bruhat product formula expresses `Φ` through the
  integrality indicator outside `S` and the factors `ΦR`, `ΦC` and `(D v).Φ`. The Fourier
  product formula expresses `Φhat` through `realFourierTransform (aR v) (ΦR v)`,
  `complexFourierTransform (aC w) (ΦC w)` and `(D v).Φhat`. Neither formula has a scalar
  prefactor, so neither involves `κ`, `CB` or `c`. The integration step does not change
  `Φ` or any local Schwartz datum.
- Nonvanishing. In each right half-plane, the two nonvanishing clauses for the archimedean
  products concern `infiniteIntegral` and `infiniteDualIntegral`. Both bodies define them
  by the same expressions in `DR`, `WR`, `WR'`, `ΦR`, `DC`, `WC`, `WC'`, `ΦC`, `aR` and
  `aC`. The two clauses for the places of `S` concern `(D v).integral` and
  `(D v).dualIntegral`. None of these clauses involves the scalar or the global integrals.

The rectangular Tate identity `RectangleTateStatement`, used for unequal ranks, is not
needed. In equal rank there is no inner integral over rectangular matrices: the
Schwartz–Bruhat function enters `equalWhittakerIntegrand` directly, through its value at
the last row of the representative.

The proof follows the integration steps of the published
`equalArchimedeanFactorizationReduction` in
[`EqualArchimedeanFactorizationReduction`](EqualArchimedeanFactorizationReduction.md). It
differs in two ways: the pointwise hypothesis is taken at the field of the conclusion, and
the quotient-product formula comes from the Library theorem instead of a premise. The local
group-scheme affineness and smoothness instances of this module are given by the same
theorems, `GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement`, as in the statement module. The measurable
space instances are the same Library instances.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein and S. Gelbart
(eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004, pp. 197–228,
`cogdell-2004-analytic-theory-gln`, §2.3, printed pp. 210–211 (PDF pp. 213–214). On p. 210
the unfolded integral `Ψ(s; W_φ, W'_φ', Φ)` over `N_n(𝔸) \ GL_n(𝔸)` is decomposed into an
Euler product for decomposable `φ`, `φ'` and `Φ`, "since the domain of integration also
naturally factors". On p. 211 Theorem 2.2 records the factorization, and the remark after
it unfolds the dual side, with the dual Whittaker functions and `Φ̂`, in the same way. The
Library's statement separates the infinite places and a finite set `S` from the unramified
places, integrates over the integral classes outside `S`, and allows a nonzero constant
from the normalization of the quotient measures. This module proves the integration
implication. It does not prove the pointwise premise `EqualPointwiseFactorizationAt F`.
