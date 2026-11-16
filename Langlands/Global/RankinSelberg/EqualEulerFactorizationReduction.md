# Reduction of the equal-rank partial Euler factorization

Module `Langlands.Global.RankinSelberg.EqualEulerFactorizationReduction`. Authors: Worker
5130, with Worker 24 (modules `EqualEulerIntegrand` and `EqualEulerSchwartzPart`).

## Content

The module contains, in the namespace `Langlands.Global.RankinSelbergGlobal`:

- the statement `EqualEulerFactorizationReductionStatement.{u, uQ}`, a `Prop`-valued
  definition:
  `UnramifiedWhittakerFactorizationStatement.{u, uQ} →
  WhittakerCellDecompositionStatement.{u} → EqualUnfoldingStatement.{u} →
  EqualEulerFactorizationStatement.{u, uQ}`;
- the theorem `equalEulerFactorizationReduction`, which proves it;
- two lemmas in the namespace `EqualEulerReduction`: `integrand_shift` and
  `setIntegral_insert`.

The three premises are:

- `UnramifiedWhittakerFactorizationStatement` (called (A) here): at a finite place
  `v ∉ S`, the `ψ`- and `ψ⁻¹`-Whittaker functions of a vector spherical outside `S`
  satisfy `W(g ι_v(h)) = W(g) W°(h; a)` whenever `g_v = 1`, where `W°` is the spherical
  Whittaker function of Shintani's formula and `a` enumerates the Satake parameters at `v`
  (Cogdell 2004, §2.2, p.206).
- `WhittakerCellDecompositionStatement` (called (B) here): for `f` integrable on
  `N_m(𝔸) \ GL_m(𝔸)` and `v ∉ S`,
  `∑_λ N(v) ^ (∑_(i<j) (λ_i - λ_j)) ∫_(U_S) f(N_m(𝔸) ι_v(ϖ ^ λ) q.out) dq = ∫_(U_(S∪{v})) f`,
  where `U_S = unipotentIntegralClasses F m S` is the set of classes with
  `g_w ∈ N_m(F_w) GL_m(𝒪_w)` at every finite `w ∉ S` (Cogdell, Fields lectures 2003,
  Lecture 7 §3, p.57).
- `EqualUnfoldingStatement` (called (U) here), the published equal-rank unfolding
  statement. Only its integrability clause is used: on a half-plane `Re s > C` with `C`
  depending only on `T`, `T'`, the equal-rank Whittaker integrand is integrable.

The theorem is a reduction. It does not prove `EqualEulerFactorizationStatement`, because
the three premises are open statements.

### The lemmas

Notation as in `EqualEulerFactorizationStatement`: `n = r + 1`, `W = W_x^ψ`,
`W' = W_(x')^(ψ⁻¹)`, `f(q) = equalWhittakerIntegrand F W W' Φ s q`, which is
`W(g) W'(g) Φ(e_n g) |det g|^s` at the class `q` of `g`. `ϖ_v = placeUniformizer v`, and
`a`, `b` are tuples with `ofTuple a` and `ofTuple b` the Satake parameters of `P` and `P'`
at `v`.

- `integrand_shift` (assumes (A)): let `A ⊇ S` be a finite set of finite places, `v ∉ A`,
  and `q ∈ U_A`. Then
  `f(N_n(𝔸) ι_v(ϖ_v ^ λ) q.out) = cellMultiplier N(v) a b s λ · f(q)`.
- `setIntegral_insert` (assumes (A) and (B)): assume `f` integrable, Satake bounds
  `HasSatakeBound P C` and `HasSatakeBound P' C'` (all Satake parameters at places outside
  the exceptional sets have absolute value at most `q_v ^ C`, respectively `q_v ^ C'`),
  and `localRadius r C C' < Re s`. Then for every finite `A ⊇ S` and every finite place
  `v ∉ A` (with `v ∉ S`),
  `∫_(U_(A ∪ {v})) f = L(s, Π_v × Π'_v) · ∫_(U_A) f`,
  where `L(s, Π_v × Π'_v) = partialEulerFactor P P' hP hP' v s`.
- `equalEulerFactorizationReduction`: the reduction. The half-plane is
  `σ = max(C₀, max(σ₂, localRadius r C C'))`, where `C₀` is the integrability bound from
  (U), `σ₂` the convergence abscissa of the partial Euler product
  (`exists_partialEulerFactor_convergence`), and `C`, `C'` Satake bounds of `P`, `P'`
  (`exists_hasSatakeBound_presentation`). For `Re s > σ` and all `x`, `x'`, `Φ` as in the
  target, the three conclusions hold, with the product value
  `p = partialEulerProduct P P' hP hP' s`.

## Provenance

Cogdell 2004 (*Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart, *An
introduction to the Langlands program*), §2.3, printed p.210, with Theorem 3.3, p.215:
for `Re s ≫ 0` the global integral factors as the integral over the places in `S` times
the unramified local factors `L(s, Π_v × Π'_v)`, `v ∉ S`. Cogdell writes this through the
factorization of the Whittaker functions and of the integral into local integrals. The
Library's statements avoid local integrals: the target is stated with the partial integral
`partialEqualWhittakerIntegral` over `U_S`, and the one-place statements (A) and (B) are
global. This module derives the target from them. The steps are internal:

1. a pointwise identity on each Iwasawa cell (module `EqualEulerPointwise`);
2. the sum over the cells at one place, which is the local unramified computation
   (module `EqualEulerLocalSum`: Shintani's formula and the Cauchy identity);
3. the exhaustion of `N_n(𝔸) \ GL_n(𝔸)` by the sets `U_A`
   (`integral_eq_hasProd_mul_setIntegral`, module `PartialIntegralExhaustion`).

The half-plane `σ` is derived: Cogdell asserts the factorization for `Re s ≫ 0` without an
explicit bound.

## Proof

- **`integrand_shift`.** By `EqualEulerIntegrand.equalWhittakerIntegrand_mk` (the generic
  characters of `W` and `W'` cancel; `ψ.complex` is a standard additive character by
  `isStandardAdditiveCharacter_of_unitary`), the integrand at the class of any `g` is
  `W(g) W'(g) Φ(e_n g) |det g|^s`. Apply this at `g = ι_v(ϖ_v ^ λ) q.out`. Since
  `q ∈ U_A` and `v ∉ A`, the component of `q.out` at `v` lies in `N_n(F_v) GL_n(𝒪_v)`, so
  the pointwise identity `integrand_localPoint_torus_mul` of `EqualEulerPointwise` applies
  (with `v ∉ S` because `S ⊆ A`). Then use `equalWhittakerIntegrand_mk` backwards at
  `q.out` and `N_n(𝔸) q.out = q`.
- **`setIntegral_insert`.** Choose tuples `a`, `b` with `ofTuple a`, `ofTuple b` the Satake
  parameters at `v` (`Eigenvalues.ofTuple_surjective`). Apply (B) with `S := A`, the place
  `v`, the uniformizer `ϖ_v` (uniformizing for `Valued.v` by
  `isUniformizingElement_valued`) and the integrable `f`. Its second conclusion is
  `HasSum (λ ↦ N(v) ^ modulusExponent λ · ∫_(U_A) f(shift λ q)) (∫_(U_(A ∪ {v})) f)`.
  For each `λ`, `setIntegral_congr_fun` (on the measurable set `U_A`) and
  `integrand_shift` give `∫_(U_A) f(shift λ q) = cellMultiplier N(v) a b s λ · ∫_(U_A) f`.
  By `zpow_modulusExponent_mul_cellMultiplier`, the summand is
  `equalRankLocalTerm a b (N(v) ^ (-s)) λ · ∫_(U_A) f`. The Satake bounds, rewritten with
  `q_v = N(v)` (`residueCardinality_eq_absNorm`), and `N(v) ≥ 2` give, by
  `hasSum_equalRankLocalTerm_eulerFactor` of `EqualEulerLocalSum`,
  `HasSum (equalRankLocalTerm a b (N(v) ^ (-s))) L(s, Π_v × Π'_v)`. Multiplying by
  `∫_(U_A) f` and using uniqueness of sums (`HasSum.unique`) gives the claim. The set
  `A ∪ {v}` appears as `Finset.cons v A _` (`Finset.cons_eq_insert`).
- **`equalEulerFactorizationReduction`.** Obtain `C₀` from
  `EqualEulerIntegrand.exists_integrable_equalWhittakerIntegrand_unitary` (which uses (U)),
  `σ₂` from `exists_partialEulerFactor_convergence`, and `C`, `C'` from
  `exists_hasSatakeBound_presentation`. For `Re s > σ`, integrability is the first, and
  summability with `HasProd` toward `p = partialEulerProduct P P' hP hP' s` the second.
  The identity is `integral_eq_hasProd_mul_setIntegral` for `f`, with the step identity
  `setIntegral_insert`, after rewriting the partial integral as the set integral over
  `U_S` (`partialEqualWhittakerIntegral_eq_setIntegral`) and commuting the product.
