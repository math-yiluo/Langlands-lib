# The partial equal-rank global Whittaker integral

This module defines one object: `partialEqualWhittakerIntegral`, the integral
`Ψ_(S∪∞)(s; W, W', Φ)` that appears in the partial Euler factorization of the equal-rank
global Rankin–Selberg Whittaker integral. It is the analogue for `m = n` of
`partialUnequalWhittakerIntegral` in `Langlands.Global.RankinSelberg.PartialWhittakerIntegrals`,
and it is built the same way. It is a concrete definition; the module asserts no
convergence and no identity.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3).

* §2.3, printed p.210 (PDF p.213): for decomposable `φ`, `φ'` and
  `Φ = ∏_v Φ_v ∈ S(𝔸^n)`, the integral
  `Ψ(s; W_φ, W'_φ', Φ) = ∫_(N_n(𝔸) \ GL_n(𝔸)) W_φ(g) W'_φ'(g) Φ(e_n g) |det g|^s dg`
  is the Euler product `∏_v Ψ_v(s; W_(φ_v), W'_(φ'_v), Φ_v)` of the local integrals
  `Ψ_v = ∫_(N_n(F_v) \ GL_n(F_v)) W_(φ_v)(g_v) W'_(φ'_v)(g_v) Φ_v(e_n g_v) |det g_v|^s dg_v`.
* Theorem 3.3, printed p.215 (PDF p.218): for unramified `π_v`, `π'_v`, `ψ_v`, with the
  `GL_n(𝒪_v)`-fixed Whittaker functions `W_o`, `W'_o` normalized by
  `W_o(e) = W'_o(e) = 1` and `Φ_o` the characteristic function of `𝒪_v^n`, one has
  `Ψ_v(s; W_o, W'_o, Φ_o) = L(s, π_v × π'_v)`.
* §4.1, printed p.219 (PDF p.222): for `m = n`,
  `I(s; φ, φ', Φ) = (∏_(v ∈ S) Ψ_v(s; W_(φ_v), W'_(φ'_v), Φ_v)) L^S(s, π × π')`, where
  Cogdell's `S` contains the archimedean places.

## The definition

Let `n = r + 1`. `partialEqualWhittakerIntegral F S W W' Φ s`, for a finite set `S` of
finite places, functions `W`, `W'` on `GL_n(𝔸)`, `Φ : RowVector F n → ℂ` and `s ∈ ℂ`, is
the Bochner integral of the existing integrand `equalWhittakerIntegrand F W W' Φ s` over
the classes `q ∈ N_n(𝔸) \ GL_n(𝔸)` whose representative `q.out` lies in
`unipotentIntegralOutside F n S`. The measure is the restriction of the same
`whittakerQuotientMeasure F n` that defines `equalWhittakerIntegral`.

* `equalWhittakerIntegrand F W W' Φ s q = W(g) W'(g) Φ(e_n g) |det g|^s` with
  `g = q.out` (module `Langlands.Global.RankinSelberg.EqualIntegrals`).
* `unipotentIntegralOutside F n S` is the set of adelic `g` with
  `g_v ∈ N_n(F_v) GL_n(𝒪_v)` at every finite place `v ∉ S` (module
  `Langlands.Global.RankinSelberg.PartialWhittakerIntegrals`). There is no condition at
  the places of `S` or at the infinite places. The set is left `N_n(𝔸)`-invariant, so
  the selected set of classes does not depend on the choice of representative. It is
  open, since each `N_n(F_v) GL_n(𝒪_v)` is open in `GL_n(F_v)`.
* `whittakerQuotientMeasure F n` (module `Langlands.Global.RankinSelberg.WhittakerIntegrals`)
  is the image of the Haar quotient measure on `N_n(F) \ GL_n(𝔸)`.

In the source's notation the domain is
`N_n(𝔸) \ (GL_n(𝔸_(S∪∞)) × ∏_(v ∉ S) N_n(F_v) GL_n(𝒪_v))`.

## Comparison with the source

Cogdell's `∏_(v ∈ S) Ψ_v` is a product of local integrals over the places of his `S`,
which contains the archimedean places. The Library's `S` contains only finite places, so
the corresponding object here is indexed by `S ∪ ∞`. It is the global integral over the
selected classes, not a product of local integrals. This avoids factoring the global
quotient measure into local measures, exactly as for `partialUnequalWhittakerIntegral`.

For the data of Theorem 3.3 the restriction carries the local integrals at `S ∪ ∞`. Let
`v ∉ S` be finite, and let the components of `W`, `W'` and `Φ` at `v` be `W_o`, `W'_o` and
`Φ_o = 1_(𝒪_v^n)`. On the selected set, `g_v = u_v k_v` with `u_v ∈ N_n(F_v)` and
`k_v ∈ GL_n(𝒪_v)`. Then

* `W_o(g_v) W'_o(g_v) = ψ_v(u_v) ψ_v(u_v)^(−1) W_o(e) W'_o(e) = 1`;
* `Φ_o(e_n g_v) = Φ_o(e_n k_v) = 1`, because `e_n u_v = e_n` and `e_n k_v` is the last
  row of a matrix in `GL_n(𝒪_v)`, so it lies in `𝒪_v^n`;
* `|det g_v|_v = 1`.

So the integrand on the selected set is the integrand at `S ∪ ∞`, and `Ψ_(S∪∞)` is that
local integral times the volumes of `N_n(F_v) \ N_n(F_v) GL_n(𝒪_v)` for `v ∉ S` (all `1`
in Cogdell's normalization `vol(GL_n(𝒪_v)) = 1`). The same volumes appear when the full
integral is factored, so the factorization identity `Ψ = Ψ_(S∪∞) · ∏_(v ∉ S) L_v` does
not depend on the normalization of the global measure. Up to this identification,
`Ψ_(S∪∞)` is Cogdell's `∏_(v ∈ S) Ψ_v` (p.219). Because Lean `∫` is total, the definition
asserts no convergence; convergence is a clause of `EqualEulerFactorizationStatement`,
which uses it.

## Provenance

The construction is internal. It restricts the Library's equal-rank integrand
`equalWhittakerIntegrand` and quotient measure `whittakerQuotientMeasure` to the
existing set `unipotentIntegralOutside`. The only source content is the interpretation
above, from Cogdell pp.210, 215 and 219.
