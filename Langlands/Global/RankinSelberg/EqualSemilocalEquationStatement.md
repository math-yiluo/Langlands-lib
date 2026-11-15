# Semi-local functional equation of the equal-rank partial Whittaker integrals

`Langlands.Global.RankinSelbergGlobal.EqualSemilocalEquationStatement` is the functional
equation of the equal-rank partial Whittaker integrals `Ψ_(S∪∞)(s; W, W', Φ)` and
`Ψ_(S∪∞)(s; W̃, W̃', Φ̂)` of a pair of cusp forms on `GL_n × GL_n` and a Schwartz–Bruhat
function: the product over the places of `S` and the infinite places of the local
functional equations. It is a Prop-valued statement. Nothing here proves it. It is the
equal-rank companion of `UnequalSemilocalEquationStatement`, whose Markdown explains the
common points in more detail. Here `n = r + 1`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3).

* §4.1, proof of Theorem 4.1, printed pp.219–220 (PDF pp.222–223): for `m = n` and
  appropriate `φ`, `φ'`, `Φ`, `I(s; φ, φ', Φ) = (∏_(v ∈ S) Ψ_v(s; W_v, W'_v, Φ_v) / L(s, π_v × π'_v)) L(s, π × π')`
  (p.219). The functional equation is derived for `m < n`, "the other case is entirely
  analogous" (p.220): the global equation `I(s; φ, φ', Φ) = I(1 − s; φ̃, φ̃', Φ̂)`
  (Theorem 2.2, p.211), the factorization of both sides, and the local functional
  equations at `v ∈ S`.
* Theorem 3.2, printed p.214 (PDF p.217), the nonarchimedean local functional equation
  for `m = n`: `Ψ(1 − s; W̃, W̃', Φ̂) = ω'(−1)^(n−1) γ(s, π × π', ψ) Ψ(s; W, W', Φ)`.
* §3.2, printed pp.216–217 (PDF pp.219–220): the archimedean factors of Jacquet and
  Shalika, `γ = ε L(1 − s, π̃ × π̃') / L(s, π × π')` (p.216), the meromorphy of the local
  integrals (Theorem 3.5) and the local functional equation for `m = n` (Theorem 3.6,
  p.217).

## The statement

The hypotheses are those of the published target
`Langlands.Global.CuspidalPairPartialGammaEquationStatement` with `t = r`, without the
presentations `Pd`, `Pd'` (they do not enter): `F`, `ψ` trivial on `F`; actual cuspidal
realizations `T`, `Td`, `T'`, `Td'` of `GL_n` with `IsContragredientOf Td.realization T.realization`
and `IsContragredientOf Td'.realization T'.realization`; presentations `P`, `P'` of `T`,
`T'` with irreducible admissible finite components (`hI`, `hI'`); a finite set `S` of
finite places containing `P.exceptional` and `P'.exceptional`, with
`FunctionalEquationComparison.FiniteAdditiveSupport ψ S`; the archimedean additive
components `aR`, `aC` and the archimedean parameters of `T`, `T'`, `Td`, `Td'`. The
functions `infiniteL` (`L_∞`), `dualInfiniteL` (`L∨_∞`) and `infiniteEpsilon` (`ε_∞`) are
defined exactly as in the target.

The conclusion: there exist `x : T.Space`, `x' : T'.Space` and `Φ : RowVector F n → ℂ` with
`IsSphericalOutside F T S x`, `IsSphericalOutside F T' S x'`, `Φ ∈ schwartzBruhat F n` and
`IsStandardOutside F n S Φ`. Put `W = cuspWhittaker F T ψ.complex x`,
`W' = cuspWhittaker F T' ψ.complex⁻¹ x'`, `Wdual = dualFunction F n W` (that is, `W̃`),
`W'dual = dualFunction F n W'` (that is, `W̃'`) and `Φhat = fourierTransform F n ψ.complex Φ`
(that is, `Φ̂`), the functions of the published `EqualUnfoldingStatement`. Then there exist
`σ : ℝ` and `A B : ℂ → ℂ` such that

1. `A` and `B` are meromorphic on `ℂ`;
2. for `σ < Re s`, `A s = partialEqualWhittakerIntegral F S W W' Φ s` and
   `B s = partialEqualWhittakerIntegral F S Wdual W'dual Φhat s`;
3. `A s ≠ 0` and `B s ≠ 0` for all `s` off a discrete set;
4. for every family `ψv` of canonical finite components of `ψ`, every family `νv` of
   measures self-dual for them and every `G` such that `G v` satisfies
   `RankinSelberg.IsPadicSymmetricGammaFactor` for the actual local components of `P`
   and `P'` at each `v ∈ S`, off a discrete set,
   `L_∞(s) B(1 − s) = (∏_(v ∈ S) G_v(q_v^(−s))) ε_∞(s) L∨_∞(1 − s) A(s)`.

For equal ranks `IsPadicSymmetricGammaFactor` is the pair relation
`IsPadicPairGammaFactor` for `(π_v, π'_v)`, the JPSS gamma factor of Theorem 3.2 without the
sign `ω'_v(−1)^(n−1)`. The module declares the same two local instances as
`EqualUnfoldingStatement`; they are Library theorems made available to instance search
and add no hypothesis. The target has two local instance bindings for the topologies of
`GL_(r+1)(F_v)` and `GL_(t+1)(F_v)`; for `t = r` they are the same instance, and this
statement binds it once.

## Why the statement holds, and its normalizations

Take pure tensors `x`, `x'`, `Φ` with spherical components at the finite `v ∉ S` and
`Φ_v = 1_(𝒪_v^n)` there, and with local data at `S ∪ ∞` whose local integrals are not
identically zero (at `v ∈ S` the JPSS integrals span `L(s, π_v × π'_v) ℂ[q_v^s, q_v^(−s)]`; at
the infinite places Jacquet–Shalika). Then:

* **Factorization.** By the arguments in the Markdown of `EqualEulerFactorizationStatement`
  and `EqualDualEulerFactorizationStatement`,
  `Ψ_(S∪∞)(s; W, W', Φ) = c ∏_(v ∈ S∪∞) Ψ_v(s; W_v, W'_v, Φ_v)` and
  `Ψ_(S∪∞)(s; W̃, W̃', Φ̂) = c ∏_(v ∈ S∪∞) Ψ_v(s; W̃_v, W̃'_v, Φ̂_v)` for `Re s ≫ 0`, with the
  same constant `c`. Here `Φ̂ = ⊗_v Φ̂_v` because `rectangleMeasure F 1 n` is the product of
  the local measures self-dual for `ψ_v` (Tate's thesis), and `Φ̂_v = 1_(𝒪_v^n)` for `v ∉ S`
  because `ψ_v` has conductor `𝒪_v`.
* **Continuation.** The local integrals are rational in `q_v^(−s)` at `v ∈ S` and
  meromorphic at the infinite places (Theorem 3.5), so `A` and `B` are meromorphic and
  `A` is not identically zero; `B` is not identically zero by the functional equation.
* **Local functional equations.** At `v ∈ S` (Theorem 3.2, local Fourier transform for
  the self-dual measure), `Ψ_v(1 − s; W̃_v, W̃'_v, Φ̂_v) = ω'_v(−1)^(n−1) G_v(q_v^(−s)) Ψ_v(s; W_v, W'_v, Φ_v)`.
  At the infinite places (Theorem 3.6), the same with
  `ε(s, π_v × π'_v, ψ_v) L(1 − s, π̃_v × π̃'_v) / L(s, π_v × π'_v)` in place of `G_v`.
* **No sign.** `∏_(v ∈ S∪∞) ω'_v(−1)^(n−1) = 1`, as in the unequal case: `ω'` is trivial
  on `F^×`, and `ω'_v(−1) = 1` at the finite `v ∉ S`.

The archimedean conventions are those of the target, as explained in the Markdown of
`UnequalSemilocalEquationStatement`: the premise inherits the target's identification of
the archimedean parameters with the Langlands parameters of the archimedean components
and its normalization of `ε_∞`.

## Choices of form

* `x`, `x'` and `Φ` are existential: the nonvanishing clause fails for `x = 0`, and the
  consumer needs one good choice. `Φ` is standard outside `S`, which the published
  `EqualEulerFactorizationStatement` and `EqualDualEulerFactorizationStatement` require.
* The clause on `G` is universal, as in the target; the gamma factor is unique
  (`IsPadicSymmetricGammaFactor.unique`).
* The statement is multiplicative and divides by nothing.
* Cogdell's `S` contains the archimedean places; here the infinite places are always kept
  in `Ψ_(S∪∞)`, `L_∞` and `ε_∞`.

## Deviations from the source

* Cogdell writes the functional equation out only for `m < n`. This statement is the
  equal-rank semi-local step of his "entirely analogous" argument, isolated as a
  property of the Library's partial integral `partialEqualWhittakerIntegral`
  (`Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral`). The global parts are
  the published `EqualAnalyticStatement`, `EqualUnfoldingStatement` and
  `EqualEulerFactorizationStatement`, and `EqualDualEulerFactorizationStatement`.
* "Appropriate `φ`, `φ'` and `Φ`" is made precise as the existence of data, spherical and
  standard outside `S`, with nonvanishing partial integrals.

## Provenance

Internal premise of Task 6190 (proof of `CuspidalPairPartialGammaEquationStatement`). It
transcribes the equal-rank form of the step "by the local functional equations, for each
`v ∈ S`" of Cogdell p.220, multiplied over `S ∪ ∞`, onto the Library's partial integrals,
the Schwartz–Bruhat space and its Fourier transform, the target's archimedean factors and
the target's hypotheses on the finite gamma factors. The derivation above is a sketch of
the standard argument and is not part of the Lean statement.
