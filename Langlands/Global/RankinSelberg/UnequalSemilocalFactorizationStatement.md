# Factorization and archimedean theory of the unequal-rank partial Whittaker integrals

`Langlands.Global.RankinSelbergGlobal.UnequalSemilocalFactorizationStatement.{u, uQ}` is
a Prop-valued statement. It is the open premise of the conditional proof of
`UnequalSemilocalEquationStatement` in the module `UnequalSemilocalEquationReduction`,
and nothing here proves it. It collects the following parts of Cogdell's proof of
Theorem 4.1:

* the factorization of the partial integrals `Ψ_(S∪∞)` and `Ψ̃_(S∪∞)` of suitable vectors
  into local integrals;
* the archimedean local theory of Jacquet and Shalika;
* the cancellation of the central signs `ω'_v(−1)^(n−1)` over `S ∪ ∞`.

The finite places of `S` enter only through local data at those places. Their
functional equation is not part of the premise, because the reduction takes it from the
Library. With `n = r + 1` and `m = t + 1`, the hypothesis is `t < r`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3).

* §4.1, proof of Theorem 4.1, printed pp.219–220 (PDF pp.222–223). For "appropriate" `φ`,
  `φ'` the global integrals factor over `S` (Cogdell's `S` contains the infinite places).
  At `v ∈ S` the local functional equations are applied, and the signs `ω'_v(−1)^(n−1)`
  cancel because `ω'` is trivial on `F^×` and unramified outside `S`.
* §3.2, printed pp.216–217 (PDF pp.219–220): the archimedean factors are the Artin–Weil
  factors of the Langlands parameters (p.216). Theorem 3.5 gives meromorphy of the
  archimedean integrals, and Theorem 3.6 the archimedean local functional equation
  `Ψ_(n−m−1)(1 − s; ρ(w_(n,m)) W̃, W̃') = ω'(−1)^(n−1) γ(s, π × π', ψ) Ψ_0(s; W, W')`,
  with `γ = ε L(1 − s, π̃ × π̃') / L(s, π × π')`.
* Theorem 3.2, printed p.214 (PDF p.217): the local integrals at a finite place are
  rational in `q_v^(−s)` (JPSS). This is used for the nonzero rational continuation of the
  chosen local integral.

## Local test data

`UnequalBlockZeroTestData ψ π σ` is defined over a nonarchimedean local field `F` with
the measurable structures of the Library's local theory, for representations `π` of
`GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)`. It records the objects over which
`UnequalRankGammaEquation` quantifies:

* `invariant`: right invariance of `unipotentHaar F t`;
* `measure`: a quotient measure on `LeftUnipotentQuotient t F`, that is, on
  `N_(t+1)(F) \ GL_(t+1)(F)`;
* `compatible`: the measure is compatible with `generalLinearHaar F t` and
  `unipotentHaar F t`;
* `functional`, `functional_ne_zero`: a nonzero Whittaker functional for `ψ` on `π`
  (`glFunctionals ψ r π`);
* `inverseFunctional`, `inverseFunctional_ne_zero`: a nonzero Whittaker functional for
  `ψ⁻¹` on `σ` (`glInverseFunctionals ψ t σ`);
* `vector`, `inverseVector`: one function `W` of the coefficient model of `π` and one
  function `W'` of the coefficient model of `σ`.

For `h : t < r`, an absolute value `abv` and an additive Haar measure `ν`:

* `D.integral h abv ν` is the Library's block-zero integral
  `unequalRankIntegralAt 0 (r − t − 1) ψ abv D.measure (rectangularMeasure ν 0 (t + 1)) W W'`,
  that is, `Ψ(s; W, W')` (the block variable is empty);
* `D.dualIntegral h abv ν` is
  `dualUnequalRankModelIntegralAt h 0 (r − t − 1) ψ abv D.measure ν π σ ℓ ℓ' W W'`, that is,
  the block-`(r − t − 1)` integral `Ψ̃(s; ρ(w_(n,m)) W̃, W̃')` for `ψ⁻¹`. Its inner variable
  ranges over `M_(n−m−1,m)(F)` with the product measure built from `ν`.

These are exactly the two integrals related by `UnequalRankGammaEquation` at block
`j = 0`, `k = r − t − 1`.

`PadicUnequalTestData K ψ π σ` is `UnequalBlockZeroTestData` over a p-adic field
`K : PadicField p`, with the canonical topology, valuative relation and local field
structure of `K.canonicalTopologicalData` and the Borel measurable structures. These are
the instances under which `RankinSelberg.IsPadicPairGammaFactor` is stated. For such
data:

* `D.integral h ν` and `D.dualIntegral h ν` use the normalized absolute value
  `normalizedAbsoluteValue K.canonicalTopologicalData`, again as in
  `IsPadicPairGammaFactor`;
* `D.HasMinusOneScalar ζ` is `HasModelMinusOneScalar σ D.inverseFunctional ζ`, that is,
  `W'(−g) = ζ W'(g)` for every function `W'` of the coefficient model of `σ`. For an
  irreducible `σ` with central character `ω'`, `ζ = ω'(−1)`.

## The statement

The hypotheses are those of `UnequalSemilocalEquationStatement`, unchanged: `F`, `ψ`
trivial on `F`, `h : t < r`, `T`, `Td`, `T'`, `Td'` with contragredience, `P`, `P'` with
irreducible admissible components `hI`, `hI'`, the finite set `S` with the exceptional
sets and `FiniteAdditiveSupport ψ S`, `aR`, `aC`, the archimedean parameters with their
specifications, and the same `infiniteL` (`L_∞`), `dualInfiniteL` (`L∨_∞`) and
`infiniteEpsilon` (`ε_∞`). The module declares the same two local instances as the
target.

The conclusion. Let `ψv` be a family of canonical finite components of `ψ`
(`IsCanonicalFiniteAdditiveComponent`), and `νv` a family of measures self-dual for them
(`Correspondence.IsSelfDualMeasure`). Then there exist `x : T.Space` and `x' : T'.Space`,
fixed by `GL(𝒪_v)` at every finite `v ∉ S` (`IsSphericalOutside`). With `W`, `W'`, `Wdual`,
`W'dual` defined as in the target, there further exist `σ : ℝ`, `Ainf Binf : ℂ → ℂ`, and
for each `v ∈ S` p-adic test data
`D v : PadicUnequalTestData (padicField v) (ψv v) π_v π'_v`. Here `π_v`, `π'_v` are the
actual local components
`((P.localComponent v).padicObject (hI v).1 (hI v).2).obj.representation`, and
similarly for `P'`. They satisfy:

1. `Ainf` and `Binf` are meromorphic on `ℂ`, and nonzero off a discrete set
   (`Filter.codiscrete ℂ`);
2. for each `v ∈ S` there is a nonzero rational function `R` with
   `HasRationalContinuation (residueCardinality v) ((D v).integral h (νv v)) R`;
3. for `σ < Re s`,
   `partialUnequalWhittakerIntegral F h S W W' s = Ainf s * ∏_(v ∈ S) (D v).integral h (νv v) s`;
4. for `σ < Re s`,
   `partialDualWhittakerIntegral F h S Wdual W'dual s = Binf s * ∏_(v ∈ S) (D v).dualIntegral h (νv v) s`;
5. for every `ζ : S → ℂˣ` with `(D v).HasMinusOneScalar (ζ v)` for all `v ∈ S`, off a
   discrete set,
   `(∏_(v ∈ S) ζ_v^r) L_∞(s) Binf(1 − s) = ε_∞(s) L∨_∞(1 − s) Ainf(s)`.

## Why the premise holds

The following sketch is the standard argument; it is not part of the Lean statement.
Take pure tensors `x`, `x'` that are spherical at every finite `v ∉ S`. Choose their local
Whittaker functions at `v ∈ S` so that `Ψ_v(s; W_v, W'_v)` is not identically zero (JPSS:
these integrals span `L(s, π_v × π'_v) ℂ[q_v^s, q_v^(−s)]`). At the infinite places,
choose `K`-finite components with nonzero archimedean integral (Jacquet–Shalika; Cogdell
Theorem 3.5 and p.218).

* **Data `D v`.** `D v` records the local Whittaker functionals for `ψ_v` and `ψ_v⁻¹`, the
  local Whittaker functions `W_v`, `W'_v` of the components of `x`, `x'`, and a compatible
  quotient measure at `v`. Clause 2 is the JPSS rationality of `Ψ_v(s; W_v, W'_v)`, which
  is nonzero by choice.
* **Factorization (clauses 3, 4).** This is the argument of the Markdown of
  `UnequalSemilocalEquationStatement`. For `Re s ≫ 0`,
  `Ψ_(S∪∞)(s; W, W') = c ∏_(v ∈ S ∪ ∞) Ψ_v(s; W_v, W'_v)` and
  `Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃') = c ∏_(v ∈ S ∪ ∞) Ψ̃_v(s; ρ(w_(n,m)) W̃_v, W̃'_v)`, with the
  same constant `c`. The constant compares the measures and contains the volumes at
  `v ∉ S`. On the inner variable of `Ψ̃`, the covolume-one measure of `M_(n−m−1,m)(𝔸)` is
  the product of the local measures self-dual for `ψ_v`, which explains the use of `νv`.
  Take `Ainf = c ∏_(v | ∞) Ψ_v` and `Binf = c ∏_(v | ∞) Ψ̃_v`.
* **Clause 1.** The archimedean integrals are meromorphic (Theorem 3.5). `Ainf` is not
  identically zero by choice, and `Binf` is not by clause 5. A meromorphic function on `ℂ`
  that is not identically zero is nonzero off a discrete set.
* **Clause 5.** Multiplying Theorem 3.6 over the infinite places gives
  `L_∞(s) Binf(1 − s) = ω'_∞(−1)^(n−1) ε_∞(s) L∨_∞(1 − s) Ainf(s)`. The central character
  `ω'` is trivial on `F^×`, and `ω'_v(−1) = 1` at finite `v ∉ S`. Hence
  `ω'_∞(−1)^(n−1) ∏_(v ∈ S) ω'_v(−1)^(n−1) = 1`. A nonzero functional determines the
  minus-one scalar of its model (`HasModelMinusOneScalar.unique`), so `ζ_v = ω'_v(−1)`,
  and `n − 1 = r`.

**Archimedean conventions.** `L_∞`, `L∨_∞` and `ε_∞` are the target's expressions, so the
premise inherits the target's normalization and its identification of the Library's
archimedean parameters with the Langlands parameters used by Jacquet–Shalika. See the
Markdown of `UnequalSemilocalEquationStatement`.

## Choices of form

* **Existential local data.** The vectors, the archimedean functions and the local data
  at `S` are existential, and the local data are recorded only through the two integrals
  the reduction needs. This is weaker than asserting the factorization for all pure
  tensors.
* **Order of quantifiers.** `ψv` and `νv` are quantified before the existential.
  Canonical components and self-dual measures are unique, so this is equivalent to
  stating the premise for the canonical ones.
* **One fused premise.** The factorization and the archimedean functional equation share
  the existential `x`, `x'`, `Ainf`, `Binf`. They are therefore stated together, and the
  sign cancellation is folded into clause 5. Clause 5 is the archimedean equation once
  `∏_(v ∈ S) ζ_v^r` is identified with `ω'_∞(−1)^(−r)`; the two agree since `ζ_v = ±1`.
* **Finite places.** No local functional equation at `v ∈ S` is assumed. The reduction
  derives it from the Library's gamma factor of the generic local components.

## Provenance

Internal premise of the proof of `UnequalSemilocalEquationStatement`, derived from
Cogdell 2004, proof of Theorem 4.1 (pp.219–220), with §3.2 (pp.216–217). The split is
ours. The premise keeps the global factorization and the archimedean theory, which the
Library does not prove. It drops the nonarchimedean functional equation, which the
Library proves.
