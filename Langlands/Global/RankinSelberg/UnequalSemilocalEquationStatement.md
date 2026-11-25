# Semi-local functional equation of the unequal-rank partial Whittaker integrals

`Langlands.Global.RankinSelbergGlobal.UnequalSemilocalEquationStatement` is the functional
equation of the partial Whittaker integrals `Ψ_(S∪∞)` and `Ψ̃_(S∪∞)` of a pair of cusp
forms on `GL_n × GL_m`, `m < n`: the product over the places of `S` and the infinite
places of the local functional equations. It is a Prop-valued statement. Nothing here
proves it. With `n = r + 1` and `m = t + 1`, the hypothesis is `t < r`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3).

* §4.1, proof of Theorem 4.1, printed pp.219–220 (PDF pp.222–223). For `m < n` and
  "appropriate" `φ`, `φ'`, the global integral factors as
  `I(s; φ, φ') = (∏_(v ∈ S) Ψ_v(s; W_v, W'_v) / L(s, π_v × π'_v)) L(s, π × π')`, and the
  dual side as
  `Ĩ(1 − s; φ̃, φ̃') = (∏_(v ∈ S) Ψ̃_v(1 − s; ρ(w_(n,m)) W̃_v, W̃'_v) / L(1 − s, π̃_v × π̃'_v)) L(1 − s, π̃ × π̃')`.
  "By the local functional equations, for each `v ∈ S`",
  `Ψ̃_v(1 − s; ρ(w_(n,m)) W̃_v, W̃'_v) / L(1 − s, π̃_v × π̃'_v) = ω'_v(−1)^(n−1) ε(s, π_v × π'_v, ψ_v) Ψ_v(s; W_v, W'_v) / L(s, π_v × π'_v)`.
  For `v ∉ S`, `ω'_v(−1) = 1`. Cogdell's `S` contains the archimedean places.
* Theorem 3.2, printed p.214 (PDF p.217), the nonarchimedean local functional equation
  `Ψ̃(1 − s; ρ(w_(n,m)) W̃, W̃') = ω'(−1)^(n−1) γ(s, π × π', ψ) Ψ(s; W, W')`, with
  `ε(s, π × π', ψ) = γ(s, π × π', ψ) L(s, π × π') / L(1 − s, π̃ × π̃')`.
* §3.2, printed pp.216–217 (PDF pp.219–220), the archimedean theory of Jacquet and
  Shalika: `L(s, π_v × π'_v) = L(s, ρ_v ⊗ ρ'_v)` and `ε(s, π_v × π'_v, ψ_v) = ε(s, ρ_v ⊗ ρ'_v, ψ_v)`
  are the Artin–Weil factors of the tensor product of the Langlands parameters, and
  `γ = ε L(1 − s, π̃ × π̃') / L(s, π × π')` (p.216). Theorem 3.5 (p.217): the local integrals
  are meromorphic, and their ratios with `L(s, π_v × π'_v)` are entire. Theorem 3.6
  (p.217): the local functional equation
  `Ψ_(n−m−1)(1 − s; ρ(w_(n,m)) W̃, W̃') = ω'(−1)^(n−1) γ(s, π × π', ψ) Ψ_0(s; W, W')`.

## The statement

The hypotheses are those of the Library target
`Langlands.Global.CuspidalPairPartialGammaEquationStatement`, specialized to `t < r`,
without the presentations `Pd`, `Pd'` of the contragredients (they do not enter):

* `F : Type u` is a number field with `[CompactSpace (AdeleQuotient F)]`, and
  `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` is trivial on `F`. This type
  consists of continuous nontrivial circle-valued characters.
* `h : t < r`; `T`, `Td` are actual cuspidal realizations of `GL_(r+1)`, and `T'`, `Td'` of
  `GL_(t+1)`, with `IsContragredientOf Td.realization T.realization` and
  `IsContragredientOf Td'.realization T'.realization`.
* `P`, `P'` are spectral presentations of `T`, `T'` (universe `uQ`) with irreducible
  admissible finite components (`hI`, `hI'`), and `S` is a finite set of finite places
  containing `P.exceptional` and `P'.exceptional`, with
  `FunctionalEquationComparison.FiniteAdditiveSupport ψ S`.
* `aR`, `aC` describe the archimedean components of `ψ` (`IsRealAdditiveComponent`,
  `IsComplexAdditiveComponent`), and `dR`, `dR'`, `dRd`, `dRd'`, `dC`, `dC'`, `dCd`, `dCd'` are
  archimedean parameters of `T`, `T'`, `Td`, `Td'` (`HasRealPlaceParameter`,
  `HasComplexPlaceParameter`).
* `infiniteL`, `dualInfiniteL` and `infiniteEpsilon` are defined exactly as in the target:
  `L_∞(s)`, `L∨_∞(s)` are the products over the real and complex places of the inverses of
  the denominators of `realPairLFactor` and `complexPairLFactor` of the parameters, and
  `ε_∞(s)` is the product of `realPairEpsilon (dR v) (dR' v) (aR v) √|a_v|` and
  `complexPairEpsilon (dC v) (dC' v) (aC v) |a_v|`.

The conclusion: there exist `x : T.Space` and `x' : T'.Space` with
`IsSphericalOutside F T S x` and `IsSphericalOutside F T' S x'`. Put
`W = cuspWhittaker F T ψ.complex x`, `W' = cuspWhittaker F T' ψ.complex⁻¹ x'`,
`Wdual = translateFunction F (r + 1) (unfoldingWeyl F h) (dualFunction F (r + 1) W)` (that
is, `ρ(w_(n,m)) W̃`) and `W'dual = dualFunction F (t + 1) W'` (that is, `W̃'`), the functions
of the Library's `UnequalUnfoldingStatement`. Then there exist `σ : ℝ` and `A B : ℂ → ℂ`
such that

1. `A` and `B` are meromorphic on `ℂ`;
2. for `σ < Re s`, `A s = partialUnequalWhittakerIntegral F h S W W' s` and
   `B s = partialDualWhittakerIntegral F h S Wdual W'dual s`;
3. `A s ≠ 0` and `B s ≠ 0` for all `s` off a discrete set (`Filter.codiscrete ℂ`);
4. for every family `ψv` of canonical finite components of `ψ`
   (`IsCanonicalFiniteAdditiveComponent`), every family `νv` of measures self-dual for them,
   and every `G` such that `G v` satisfies `RankinSelberg.IsPadicSymmetricGammaFactor` for
   the actual local components of `P` and `P'` at `v`, for each `v ∈ S`, off a discrete set,
   `L_∞(s) B(1 − s) = (∏_(v ∈ S) G_v(q_v^(−s))) ε_∞(s) L∨_∞(1 − s) A(s)`, where
   `G_v(q_v^(−s))` is `RatFunc.eval` of `G v` at `spectralPoint (residueCardinality v) s`.

So `A` and `B` are the meromorphic continuations of `Ψ_(S∪∞)(s; W, W')` and
`Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃')`. The hypotheses on `ψv`, `νv` and `G` are copied from the
target. Since `t < r`, `IsPadicSymmetricGammaFactor` is the pair relation
`IsPadicPairGammaFactor` for `(π_v, π'_v)`: `G v` is the JPSS gamma factor
`γ(s, π_v × π'_v, ψ_v)` of Theorem 3.2, without the sign `ω'_v(−1)^(n−1)`. The module
declares the same two local instances as `UnequalUnfoldingStatement` (the Library's
theorems `GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement` made available to instance search). They add
no hypothesis.

## Why the statement holds, and its normalizations

Let `x`, `x'` be pure tensors whose components at every finite `v ∉ S` are spherical,
with nonzero local components chosen as follows. At `v ∈ S`, choose `W_v`, `W'_v` with
`Ψ_v(s; W_v, W'_v)` not identically zero; JPSS show that these integrals span
`L(s, π_v × π'_v) ℂ[q_v^s, q_v^(−s)]`. At the infinite places, choose `K`-finite `W_v`, `W'_v`
with `Ψ_v` not identically zero (Jacquet–Shalika; see Theorem 3.5 and the remarks on
p.218).

* **Factorization.** As explained in the Markdown of `UnequalEulerFactorizationStatement`
  and `UnequalDualEulerFactorizationStatement`, `Ψ_(S∪∞)(s; W, W') = c ∏_(v ∈ S∪∞) Ψ_v(s; W_v, W'_v)`
  and `Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃') = c ∏_(v ∈ S∪∞) Ψ̃_v(s; ρ(w_(n,m)) W̃_v, W̃'_v)` for
  `Re s ≫ 0`. The constant `c` is the same on both sides: it compares
  `whittakerQuotientMeasure` with the product of local measures and contains the local
  volumes of `N_m(F_v) \ N_m(F_v) GL_m(𝒪_v)` at `v ∉ S`. The extra inner integral of `Ψ̃`
  is over `M_(n−m−1,m)(𝔸)` with the covolume-one measure, which is the product of the
  local measures self-dual for `ψ_v` (Tate's thesis); at `v ∉ S` it contributes the
  volume of `M_(n−m−1,m)(𝒪_v)`, which is one because `ψ_v` has conductor `𝒪_v`.
* **Continuation.** Each local integral is a rational function of `q_v^(−s)` at `v ∈ S`
  (JPSS) and meromorphic at the infinite places (Theorem 3.5). So the right-hand sides
  give meromorphic `A` and `B`, and `A` is not identically zero. `B` is not identically
  zero by the functional equation below.
* **Local functional equations.** At `v ∈ S`, Theorem 3.2 with the self-dual measure for
  `ψ_v` on the inner variable gives `Ψ̃_v(1 − s) = ω'_v(−1)^(n−1) G_v(q_v^(−s)) Ψ_v(s)`. At
  the infinite places, Theorem 3.6 gives
  `Ψ̃_v(1 − s) = ω'_v(−1)^(n−1) ε(s, π_v × π'_v, ψ_v) L(1 − s, π̃_v × π̃'_v) / L(s, π_v × π'_v) Ψ_v(s)`.
* **No sign.** `∏_(v ∈ S∪∞) ω'_v(−1)^(n−1) = 1`. Indeed `ω'` is trivial on `F^×`, so
  `∏_v ω'_v(−1) = 1`, and `ω'_v(−1) = 1` for finite `v ∉ S`, where `π'_v` is unramified
  (p.220).
* Multiplying the local equations and the factor `L_∞(s)` gives the identity of the
  statement off the poles of the factors involved, a discrete set.

The statement is multiplicative: it divides by nothing, and it does not require
knowing the zeros of `L_∞`, `L∨_∞` or `ε_∞`.

**Archimedean conventions.** `L_∞`, `L∨_∞` and `ε_∞` are the expressions of the target, so
the premise inherits the target's normalization: the archimedean pair factors are the
Library's factors of the tensor product of the Weil-group parameters
(`Langlands.LocalFactor.ArchimedeanPairFactor`), with `ε` for the additive character
`x ↦ ψ_v(x)` described by `aR v`, `aC v` and the self-dual measure (scaling `√|a|` at a real
place, `|a|` at a complex place). This is the Jacquet–Shalika definition (p.216).
`HasRealPlaceParameter` and `HasComplexPlaceParameter` say that the `K`-finite vectors of
the standard module of the blocks embed equivariantly into the realization at `v`. The
archimedean component is irreducible, so it is this standard module, and the blocks are
its Langlands parameter. The identity of the statement uses that the Library's
correspondence between blocks and standard modules is the Langlands classification in
the normalization used by Jacquet–Shalika. The target rests on the same identification,
and the premise inherits it; a proof must supply it.

## Choices of form

* **Existential vectors.** The vectors `x`, `x'` are existential. For `x = 0` the
  integrals vanish, so the nonvanishing clause cannot hold for all spherical vectors.
  The proof of the target needs only one good pair.
* **Uniform `G`.** The clause on `G` is universal, as in the target. The gamma factor is
  unique (`IsPadicSymmetricGammaFactor.unique`), so this is no stronger than asserting it
  for one choice.
* **Half-plane.** `σ` depends on the chosen vectors. The clauses for `A` and `B` are on the
  same half-plane `σ < Re s`; `B` is then evaluated at `1 − s`.
* **`S`.** Cogdell's `S` contains the archimedean places. Here `S` is a finite set of
  finite places, and the infinite places are always kept in `Ψ_(S∪∞)`, `L_∞` and `ε_∞`.

## Deviations from the source

* Cogdell combines the global and local equations in one computation. This statement
  isolates the semi-local part, the product of the local equations at `S ∪ ∞`, as a
  property of the partial integrals `Ψ_(S∪∞)`, `Ψ̃_(S∪∞)` of the Library
  (`Langlands.Global.RankinSelberg.PartialWhittakerIntegrals`). The global parts
  (analytic properties, unfolding, Euler factorizations) are the Library's
  `UnequalAnalyticStatement`, `UnequalUnfoldingStatement`,
  `UnequalEulerFactorizationStatement` and `UnequalDualEulerFactorizationStatement`.
* Cogdell's "appropriate `φ` and `φ'`" is made precise as the existence of spherical
  vectors outside `S` with nonvanishing partial integrals.

## Provenance

Internal premise of the proof of `CuspidalPairPartialGammaEquationStatement`. It
transcribes the step "by the local functional equations, for each `v ∈ S`" of Cogdell
p.220, multiplied over `S ∪ ∞`, onto the Library's partial integrals, the target's
archimedean factors and the target's hypotheses on the finite gamma factors. The
derivation above is a sketch of the standard argument. It is not part of the Lean
statement.
