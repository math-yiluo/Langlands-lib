# Reduction of the equal-rank semi-local functional equation

Module `Langlands.Global.RankinSelberg.EqualSemilocalReduction`.

## 1. Content and status

The published statement
`Langlands.Global.RankinSelbergGlobal.EqualSemilocalEquationStatement.{u, uQ}` (module
[`EqualSemilocalEquationStatement`](EqualSemilocalEquationStatement.md), called (E) here) is
the functional equation of the equal-rank partial Whittaker integrals
`Ψ_(S∪∞)(s; W, W', Φ)` and `Ψ_(S∪∞)(s; W̃, W̃', Φ̂)`. It is the product, over the places of
`S` and the infinite places, of the local functional equations. This module contains, in the
namespace `Langlands.Global.RankinSelbergGlobal`:

* the Prop-valued premise `EqualSemilocalFactorizationStatement.{u, uQ}` (Section 3);
* the statement `EqualSemilocalReductionStatement.{u, uQ}`, the implication
  `EqualSemilocalFactorizationStatement.{u, uQ} → EqualSemilocalEquationStatement.{u, uQ}`;
* the theorem `equalSemilocalReduction : EqualSemilocalReductionStatement.{u, uQ}`, which
  proves it (Section 5);
* the structure `EqualLocalTestData` of local test data at a p-adic place, with its local
  integrals and two lemmas (Section 4);
* analytic helper lemmas in the namespace `EqualSemilocalReduction` (Section 4).

The theorem is a **conditional reduction**. It does not prove (E): its premise is an open
statement, proved nowhere in the Library. It is an intermediate result towards (E), whose
unconditional proof stays open.

The premise is the part of the argument that the Library does not prove: the
factorization of the partial integrals into local integrals and the archimedean local theory
of Jacquet and Shalika. The finite local theory at the places of `S` is **not** assumed. It
comes from the Library: the rationality of the local integrals from the theorem
`RankinSelberg.equalRankAnalytic` (JPSS), and the local functional equation from the
gamma-factor hypothesis on `G` that (E) itself makes.

## 2. Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3):

* §4.1, proof of Theorem 4.1, printed pp.219–220: for appropriate `φ`, `φ'`, `Φ` the global
  integral factors as `∏_(v ∈ S) Ψ_v(s; W_v, W'_v, Φ_v)` times partial L-functions (p.219),
  and the functional equation follows from the local functional equations at the places of
  `S` (p.220; the equal-rank case is "entirely analogous");
* Theorem 3.2, printed p.214: the nonarchimedean local functional equation for `m = n`,
  `Ψ(1 − s; W̃, W̃', Φ̂) = ω'(−1)^(n−1) γ(s, π × π', ψ) Ψ(s; W, W', Φ)`;
* §3.2, printed pp.216–217: the archimedean theory of Jacquet and Shalika, the meromorphy
  of the archimedean integrals (Theorem 3.5) and their local functional equation
  (Theorem 3.6).

## 3. The premise `EqualSemilocalFactorizationStatement`

**Binders.** The premise takes exactly the binders and hypotheses of (E), with the same
`classical` elaboration, the same two local scheme instances and the same `let`-definitions
of `infiniteL` (`L_∞`), `dualInfiniteL` (`L∨_∞`) and `infiniteEpsilon` (`ε_∞`), copied
unchanged. It then quantifies over a family `ψv` of canonical finite components of `ψ`
(`IsCanonicalFiniteAdditiveComponent ψ v (ψv v)`) and a family `νv` of measures self-dual
for them (`Correspondence.IsSelfDualMeasure`), as clause 4 of (E) does. Both families exist
and are unique, so this universal quantifier is harmless.

**Conclusion.** There are `x : T.Space`, `x' : T'.Space` and `Φ : RowVector F (r + 1) → ℂ`
with `IsSphericalOutside F T S x`, `IsSphericalOutside F T' S x'`,
`Φ ∈ schwartzBruhat F (r + 1)` and `IsStandardOutside F (r + 1) S Φ`. With `W`, `W'`,
`Wdual`, `W'dual`, `Φhat` defined as in (E), there are `σ : ℝ`, `Z Zd : ℂ → ℂ`, `κ : ℂ` and
local test data `D v`, for `v ∈ S`, such that:

1. `Z` and `Zd` are meromorphic on `ℂ` and nonzero off a discrete set;
2. (archimedean functional equation) off a discrete set,
   `L_∞(s) Zd(1 − s) = κ ε_∞(s) L∨_∞(1 − s) Z(s)`;
3. `D v : EqualLocalTestData (padicField v) (ψv v) (νv v) π_v π'_v`, where `π_v`, `π'_v` are
   the actual local components
   `((P.localComponent v).padicObject (hI v).1 (hI v).2).obj.representation` and the same
   for `P'`, the representations that clause 4 of (E) uses. The type is elaborated under the
   same two `letI` bindings of the canonical topologies of `F_v` and `GL_(r+1)(F_v)` as in (E);
4. for each `v ∈ S` and each `a : ℝ` there is `s` with `a < Re s` and
   `(D v).integral s ≠ 0`, and the same for `(D v).dualIntegral`;
5. (cancellation of the signs) for every `ζ : S → ℂˣ` such that `ζ v` is the scalar by which
   `−1` acts on the model of `π'_v` (`(D v).HasMinusOneScalar (ζ v)`),
   `κ ∏_(v ∈ S) ζ_v^r = 1`;
6. (factorization) for `σ < Re s`,
   `partialEqualWhittakerIntegral F S W W' Φ s = Z(s) ∏_(v ∈ S) (D v).integral s` and
   `partialEqualWhittakerIntegral F S Wdual W'dual Φhat s = Zd(s) ∏_(v ∈ S) (D v).dualIntegral s`.

**Why the premise holds (sketch, not part of the Lean).** This is the standard argument of
the statement Markdown of (E), section "Why the statement holds". Take pure tensors `x`, `x'`,
`Φ`, spherical and standard outside `S`, whose local data at `S` are those of `D v` and whose
archimedean local integrals are not identically zero (Jacquet–Shalika). Then for `Re s ≫ 0`
the partial integrals are `c ∏_(v ∈ S∪∞)` of the local integrals, with the same constant `c`
for `(W, W', Φ)` and `(W̃, W̃', Φ̂)`; `Φ̂ = ⊗ Φ̂_v` for the self-dual measures. Put
`Z = c ∏_(v | ∞) Ψ_v(s; W_v, W'_v, Φ_v)` and `Zd = c ∏_(v | ∞) Ψ_v(s; W̃_v, W̃'_v, Φ̂_v)`; they
are meromorphic (Theorem 3.5). The archimedean local functional equations (Theorem 3.6)
give clause 2 with `κ = ∏_(v | ∞) ω'_v(−1)^r` (here `n − 1 = r`); the constant `c` cancels.
Clause 5 is `∏_(v ∈ S∪∞) ω'_v(−1)^r = 1`: the central character `ω'` is trivial on `F^×`
and `ω'_v(−1) = 1` at the finite places outside `S`. The premise inherits from (E) the
identification of the Library's archimedean parameters and of `ε_∞` with those of
Jacquet–Shalika.

**Choices of form.**

* One merged premise. Factorization, archimedean functional equation and sign are the
  three facts of the argument that need the global and archimedean theory; they share the
  witnesses `x`, `x'`, `Φ`, `Z`, `Zd`, `κ`, `D`, so they are stated together.
* `Z`, `Zd` absorb the archimedean integrals and all global constants; the premise names no
  archimedean integral.
* The local data `D v` carry the Whittaker functionals `ℓ`, `ℓ'` and the Fourier transform
  `Φ̂_v` of `Φ_v`. The local measure on `N \ GL_(r+1)(F_v)` is `unipotentQuotientHaar`, the
  absolute value is the normalized one; these are the normalizations of
  `IsPadicPairGammaFactor`. Any other normalization changes the local integrals by
  constants, which `Z`, `Zd` absorb.
* Clauses 4 and 5 replace nothing in (E): clause 4 is needed for the rational continuations
  to be nonzero, clause 5 for the sign `∏ ω'_v(−1)^r` of the local equations to cancel.
  The premise does not assume rationality or the functional equation at `v ∈ S`.

**Provenance (internal).** The premise is ours. It isolates the factorization step of
Cogdell p.219 (for the partial integrals of the Library, `partialEqualWhittakerIntegral`,
keeping the places of `S ∪ ∞`), the archimedean functional equation (Theorem 3.6, multiplied
over the infinite places) and the global triviality of `ω'(−1)`. The unequal-rank companion,
the reduction of `UnequalSemilocalEquationStatement` in module
`UnequalSemilocalEquationReduction`, uses a premise of the same existential shape
(`UnequalSemilocalFactorizationStatement`).

## 4. Local test data and helpers

**`EqualLocalTestData K ψ ν π σ`** (section `PadicLocal`). For a p-adic field `K` with its
canonical topology, a nontrivial additive character `ψ`, an additive Haar measure `ν` and
representations `π`, `σ` of `GL_(r+1)(K)`: nonzero Whittaker functionals `ℓ` (for `ψ`) and
`ℓ'` (for `ψ⁻¹`), vectors `f`, `f'` of their coefficient models (the Whittaker functions
`W_v`, `W'_v`), a Schwartz–Bruhat function `Φ` on `K^(r+1)` and `Φhat` with
`IsRowFourierPair ψ ν Φ Φhat`. The section declares local instances for the canonical
topology, valuative relation, local-field structure and Borel measurable structures; they
are the instances that `IsPadicPairGammaFactor` binds with `letI`.

* `integral D` is `equalRankModelIntegral ψ |·|_K μ π σ ℓ ℓ' f f' Φ`, and `dualIntegral D`
  is `dualEqualRankModelIntegral ψ |·|_K μ π σ ℓ ℓ' f f' Φhat`, with `|·|_K` the normalized
  absolute value and `μ = unipotentQuotientHaar K r`.
* `HasMinusOneScalar D ζ` is `HasModelMinusOneScalar σ ℓ' ζ`.
* `exists_continuations`: if `π`, `σ` are irreducible and admissible, both integrals have
  rational continuations in `q^(−s)` (`HasRationalContinuation`). `π` is generic for `ψ`
  (`ℓ ≠ 0`), so of Whittaker type (`isOfWhittakerType_of_isGeneric`); for `σ` the same with
  `ψ.scale (−1)` and `standardCharacter_scale_neg_one`. `equalRankAnalytic` applied to
  `(π, σ)` and to the dual pair `(inverseTransposePullback π, inverseTransposePullback σ)`
  with the dual functionals (`isOfWhittakerType_firstDual`, `isOfWhittakerType_secondDual`,
  `firstDualFunctional_ne_zero`, `secondDualFunctional_ne_zero`), and
  `unipotentQuotientHaar_isCompatible`, gives the two continuations.
* `exists_gammaEquation`: if `IsPadicSymmetricGammaFactor K ψ ν π σ G`, there are `ζ` with
  `HasMinusOneScalar D ζ` and continuations `R`, `Rd` of the two integrals with
  `GammaFunctionalEquation q ζ r G R Rd`. For equal ranks the symmetric relation is
  `IsPadicPairGammaFactor` (`ite_eq_left`), which unfolds to `IsPairGammaFactor` and then
  to `IsEqualRankGammaFactor` (`isPairGammaFactor_self`). Its last clause, at
  `μ = unipotentQuotientHaar` and the functionals of `D`, gives `ζ` and, for `f`, `f'`, `Φ`,
  a Fourier transform `Φh` with the equation; `Φh = Φhat` by `IsRowFourierPair.unique`.

**Analytic helpers** (namespace `Langlands.Global.RankinSelbergGlobal.EqualSemilocalReduction`
unless an imported namespace is specified).

* `Langlands.Global.CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub`,
  imported from `CuspidalPairPartialGammaGlobalReduction`: a property holding
  off a discrete set holds at `1 − s` off a discrete set.
* `eventually_ne_zero_of_analyticAt`: a function meromorphic on `ℂ`, analytic and nonzero at
  one point, is nonzero off a discrete set.
* `differentiable_spectralPoint`, `analyticAt_polynomial_spectralPoint`: `q^(−s)`, and a
  polynomial in it, are entire for `q > 0`.
* `eventually_polynomial_spectralPoint_ne_zero`: a nonzero polynomial in `q^(−s)`, `q > 1`,
  is nonzero off a discrete set (`finite_spectralPoint_roots` gives a point where it is
  nonzero).
* `ratEval_eq_div`, `meromorphicOn_ratEval`, `eventually_ratEval_ne_zero`: evaluation of a
  rational function at `q^(−s)` is numerator over denominator; it is meromorphic on `ℂ`,
  and nonzero off a discrete set if the rational function is nonzero and `q > 1`.

## 5. The proof of `equalSemilocalReduction`

Introduce the premise and the binders of (E).

* **Components.** `ψ0 = canonicalFiniteAdditiveComponent ψ hdiag` is a family of canonical
  components (`isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent`), and
  `ν0 v = localSelfDualHaar (ψ0 v)` is self-dual (`isSelfDual_localSelfDualHaar`). Apply the
  premise to `ψ0`, `ν0`; it gives `x`, `x'`, `Φ` (the witnesses of (E)) and `σ`, `Z`, `Zd`,
  `κ`, `D` with clauses 1–6.
* **Continuations.** `q_v > 1` (private lemma `one_lt_residueCardinality`, from
  `Langlands.Global.CuspidalPairEulerConvergence.two_le_residueCardinality`). For each `v ∈ S` the actual
  local components are irreducible and admissible (the property of `padicObject`), so
  `exists_continuations` gives rational functions `R v`, `Rd v` with
  `(D v).integral s = R_v(q_v^(−s))` for `Re s > a_v` and
  `(D v).dualIntegral s = Rd_v(q_v^(−s))` for `Re s > ad_v`. Clause 4 shows `R v ≠ 0` and
  `Rd v ≠ 0`. Let `M` bound all `max a_v ad_v` (`Finite.exists_le`).
* **Witnesses.** `σ' = max σ M`, `A(s) = Z(s) ∏_(v ∈ S) R_v(q_v^(−s))` and
  `B(s) = Zd(s) ∏_(v ∈ S) Rd_v(q_v^(−s))`.
* **Clauses 1–3 of (E).** `A`, `B` are meromorphic (`meromorphicOn_ratEval`,
  `MeromorphicOn.fun_prod`). For `Re s > σ'`, clause 6 and the continuations give
  `A s = partialEqualWhittakerIntegral F S W W' Φ s`, and the same for `B`. `A`, `B` are
  nonzero off a discrete set by clause 1, `eventually_ratEval_ne_zero` and
  `Filter.eventually_all` over the finite type `S`.
* **Clause 4 of (E).** Let `ψv`, `νv`, `G` be as in (E). Canonical components are unique
  (private lemma `canonicalComponent_unique`: `IsCanonicalFiniteAdditiveComponent`
  determines the values of the character), so `ψv = ψ0`;
  self-dual measures are unique (`existsUnique_localSelfDualMeasure`), so `νv = ν0`. For
  `v ∈ S`, `exists_gammaEquation` applied to the hypothesis on `G v` and to `D v` gives
  `ζ v`, continuations `R1 v`, `Rd1 v` and `GammaFunctionalEquation q_v (ζ v) r (G v) (R1 v) (Rd1 v)`.
  By uniqueness of rational continuations (`HasRationalContinuation.unique`, `q_v > 1`),
  `R1 v = R v` and `Rd1 v = Rd v`. Clause 5 gives `κ ∏ ζ_v^r = 1`. Off a discrete set
  (clause 2, and nonvanishing of the denominators of `R v` at `q_v^(−s)`, of `Rd v` at
  `q_v^(−(1−s))` via `CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub`, and of `G v` at `q_v^(−s)`), the local
  equations give `Rd_v(q_v^(−(1−s))) = ζ_v^r G_v(q_v^(−s)) R_v(q_v^(−s))`. Multiplying over
  `S` (`Finset.prod_mul_distrib`, `Finset.prod_coe_sort` to pass from `∏_(v ∈ S)` to the
  product over the subtype) turns `L_∞(s) B(1 − s)` into
  `L_∞(s) Zd(1 − s) ∏ ζ_v^r ∏ G_v ∏ R_v`, and `linear_combination` with clause 2 and
  clause 5 gives `(∏_(v ∈ S) G_v(q_v^(−s))) ε_∞(s) L∨_∞(1 − s) A(s)`.

The theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

## 6. The retained premise

The only retained premise is `EqualSemilocalFactorizationStatement`. Proving it needs:

* the factorization of the global Whittaker functions of pure tensors into local Whittaker
  functions, and of the partial integral into local integrals (not in the Library);
* the archimedean Rankin–Selberg theory of Jacquet and Shalika: meromorphy and the local
  functional equation of the archimedean integrals, in the normalization of the target's
  `realPairEpsilon`, `complexPairEpsilon`, `realPairLFactor` and `complexPairLFactor` (not in
  the Library);
* the existence of local data with nonvanishing integrals and the global triviality of
  `ω'(−1)`.

The codiscrete reflection lemma is imported from
`CuspidalPairPartialGammaGlobalReduction`.
