# Change of additive character for the epsilon factor of pairs of equal rank

Author: Worker 818. This module, in namespace `Langlands.RankinSelberg`,
defines one statement, `EqualRankEpsilonCharacterChangeStatement`. It is not
proved here. The statement says how the epsilon factor of a pair of equal rank
changes when the additive character `ψ` is replaced by `ψ^a(x) = ψ(ax)`,
`a ∈ Fˣ`. Let `π`, `σ` be irreducible admissible representations of
`GL_n(F)`, `n = r + 1`, with central characters `ω_π`, `ω_σ`. Use for each
character the Haar measure on `F` that is self-dual for it. Then

`ε(s, π × σ, ψ^a) = ω_π(a)^n ω_σ(a)^n |a|^(n²(s - 1/2)) ε(s, π × σ, ψ)`.

The module complements `PairFactorCharacterChangeStatement`, which covers
unequal ranks only (Cogdell and Piatetski-Shapiro 1994, Lemma 2.1, `m < n`).
It does not change that module.

## Provenance

This is an **internal derived statement**. No original source for the p-adic
equal-rank formula was found in the project literature, so none is cited as
its source. The formula is derived below from the equal-rank JPSS functional
equation as the Library formalizes it (`EqualRankEpsilonEquation`), and the
section Derivation lists what a proof must establish.

- **Not cited as a source.** Cogdell and Piatetski-Shapiro 1994, Lemma 2.1,
  assumes `m < n`. Its local equation has no Schwartz-Bruhat function and no
  Fourier transform. It is not used here as an equal-rank theorem.
- **Comparison: the same computation at an Archimedean place.** H. Jacquet,
  *Archimedean Rankin-Selberg integrals*, Contemp. Math. 489 (2009)
  (registered as `jacquet-2009-archimedean-rankin-selberg`; author-posted
  file, PDF page = printed page), Remark 2.2, pp. 7-8, treats `F = ℝ` or `ℂ`.
  "Following Cogdell and Piatetski-Shapiro, we remark that the assertions of
  the theorem for a given ψ imply the assertions are true for any ψ. Indeed,
  consider for instance the case n = n′." With
  `m = diag(a^(n-1), …, a, 1)`, `W_m(g) = W(mg)` and `m w_n = a^(n-1) w_n m⁻¹`,
  he finds `Ψ(s, W_m, W'_m, Φ) = δ_n(m) |a|^(-s n(n-1)/2) Ψ(s, W, W', Φ)`. He
  stresses that the Fourier transform for `ψ_a` with self-dual measure is
  `|a|^(n/2) Φ̂(aX)`. He then gets
  `γ(s, π × π', ψ_a) = ω_π ω_π'(a)^n |a|^(n²(s-1/2)) γ(s, π × π', ψ)` and
  checks the case `n = 1` against Tate's
  `γ(s, χ, ψ_a) = χ(a) |a|^(s-1/2) γ(s, χ, ψ)`. The Derivation below follows
  this computation. It replaces the Archimedean integrals by the Library's
  p-adic integrals, and Jacquet's gamma factor by the epsilon monomial and
  the L-polynomials of the Library.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data and `q`
is its residue cardinality. `ψ` is a `UnitaryAdditiveCharacter` of `F`, that
is, continuous and nontrivial. `ψ.scale a` is the published character
`x ↦ ψ(a x)` (module `HarmonicAnalysis.CharacterTransport`). `ord` is
`F.canonicalTopologicalData.ord`, the normalized valuation, and
`|a| = F.canonicalTopologicalData.normalizedAbs a = q^(-ord a)`.
`LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ` is the
type of Haar measures `ν` on `F` that are self-dual for `ψ`: the Fourier
transform `f̂(y) = ∫ ψ(xy) f(x) dν(x)` satisfies `f̂̂(x) = f(-x)`
(`HarmonicAnalysis.IsSelfDual`).

`IsPadicSymmetricEpsilonFactor F ψ ν π σ e`, `e = (c, m) : ℂˣ × ℤ`, means
`ε(s, π × σ, ψ) = c q^(-ms)` (module `PadicPairFactors`). For equal ranks it
reads `π` first. It is then `IsPadicPairEpsilonFactor F ψ ν π σ e`, the
relation `IsEqualRankEpsilonFactor` (module `EpsilonFactor`) for the
normalized absolute value and `q`. That relation says:

- a quotient measure on `N_n \ GL_n(F)` compatible with the Haar measures of
  the module exists;
- `π` has a nonzero Whittaker functional `ℓ` for `ψ`, and `σ` one, `ℓ'`, for
  `ψ⁻¹`;
- for every compatible quotient measure `μ` and every pair of nonzero
  functionals `ℓ`, `ℓ'`, `EqualRankEpsilonEquation` holds with `c` and `m`.

`EqualRankEpsilonEquation` (JPSS Theorem 2.7(iii)) says that there are
`ζ : ℂˣ` and polynomials `P`, `P^∨` with the following properties:

- `ζ` is the scalar by which `-1` acts on the Whittaker model of `σ`
  (`HasModelMinusOneScalar`);
- `P` is the normalized generator of the rational continuations of the
  integrals (`equalRankRationalValues`), and `P^∨` that of the dual integrals
  (`dualEqualRankRationalValues`);
- for all model vectors `W`, `W'` and every Schwartz-Bruhat function `Φ` on
  `Fⁿ` there are a Schwartz-Bruhat function `Φ̂` and rational functions `R`,
  `R^∨` with:
  - `IsRowFourierPair ψ ν Φ Φ̂`, that is,
    `Φ̂(y) = ∫ ψ(Σ x_i y_i) Φ(x) dνⁿ(x)`;
  - `R` the continuation of
    `Ψ(s, W, W', Φ) = ∫_(N_n \ GL_n) W(g) W'(g) Φ(e_n g) |det g|^s dμ(g)`,
    where `e_n g` is the last row of `g`;
  - `R^∨` the continuation of the same integral for `ψ⁻¹`, taken of
    `W̃(g) = W(w_n ᵗg⁻¹)`, `W̃'(g) = W'(w_n ᵗg⁻¹)` and `Φ̂`;
  - with `X(s) = q^(-s)`, the identity
    `P^∨(X(1-s)) R^∨(X(1-s)) = ζ^(n-1) c X(s)^m P(X(s)) R(X(s))`
    (`NormalizedFunctionalEquation`).

In the Library the rank is written `n + 1`; here `n` is the rank.

`EqualRankEpsilonCharacterChangeStatement` quantifies over:

- every prime `p`, every `F : PadicField p` (universe `uF`) and every
  `r : ℕ`, with `n = r + 1`;
- representations `π` (universe `uV`) and `σ` (universe `uW`) of
  `GL_(r+1)(F)` that are irreducible (`Representation.IsIrreducible`) and
  admissible (`Langlands.IsAdmissible`, which includes smoothness);
- characters `ωπ ωσ : Fˣ →* ℂˣ` with
  `Classification.HasGLCentralCharacter F (r + 1) π ωπ` and the same for `σ`
  and `ωσ` (the scalar matrix `b · 1` acts by `ωπ(b)`, resp. `ωσ(b)`);
- every `ψ`, every `ν : SelfDualHaar ψ`, every `a : Fˣ`, every
  `ν' : SelfDualHaar (ψ.scale a)` and every `e : ℂˣ × ℤ`.

From `IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e` it concludes that there
is `e'` with:

- `IsPadicSymmetricEpsilonFactor F (ψ.scale a) ν'.val π σ e'`, for the same
  representations `π`, `σ`;
- `e'.2 = e.2 + (r + 1)(r + 1) · ord a`;
- `e'.1 = e.1 · ωπ(a)^(r+1) · ωσ(a)^(r+1) · |a|^(-(r+1)(r+1)/2)`.

The power `|a|^(-(r+1)(r+1)/2)` is the complex power of the positive real
number `|a|`, so it is the positive real power.

## Derivation

Write `n = r + 1`, `d = d_a = characterChangeElement a r = diag(a^r, …, a, 1)`
(module `Whittaker.CharacterChange`; it is Jacquet's `m` and the source's
`a_n(a)`) and `ω = ω_π(a) ω_σ(a)`.

**Models.** If `W` is a Whittaker function for `ψ`, then `W_a(g) = W(dg)` is
one for `ψ^a`, because `d u d⁻¹` multiplies the superdiagonal of `u` by `a`.
In the Library, `ℓ ↦ ℓ ∘ π(d)` is a bijection from the functionals of `π`
for `ψ` to those for `ψ^a` (`characterChangeFunctionalEquiv`). The map
`ℓ' ↦ ℓ' ∘ σ(d)` does the same for `ψ⁻¹` and `(ψ^a)⁻¹`
(`characterChangeInverseFunctionalEquiv`). So the nonzero functionals for
`ψ^a` are exactly the `ℓ ∘ π(d)`, `ℓ' ∘ σ(d)`, and their models are the
functions `W_a`, `W'_a`. The minus-one scalar `ζ` is unchanged, because
`-1` is central.

**The integral.** Change `g` to `d⁻¹g`. The last row is unchanged,
`e_n d⁻¹ = e_n`, and `|det g|^s` becomes `|det d|^(-s) |det g|^s`. Left
translation by `d` on `N_n \ GL_n` multiplies the quotient measure by a
positive constant `κ`: the character-change modulus of the published
`HasCharacterChangeMeasureLaw`, which `characterChangeCompatibleMeasure`
proves for every compatible quotient measure (module
`CharacterChangeMeasure`). Hence

`Ψ(s, W_a, W'_a, Φ) = κ |det d|^(-s) Ψ(s, W, W', Φ)`, with `|det d| = |a|^(n(n-1)/2)`.

This is Jacquet's first identity, where `κ = δ_n(m)`.

**The equal-rank Fourier input.** This input is absent for unequal ranks.
The functional equation for `ψ^a` uses the Fourier transform for `ψ^a` and
`ν'`. A Haar measure `cν` is self-dual for `ψ^a` exactly when
`c = |a|^(1/2)`: the transform for `ψ^a` and `cν` is `c f̂(a y)`, and
applying it twice gives `c² |a|⁻¹ f(-x)`. So `ν' = |a|^(1/2) ν` and

`Φ̂_a(y) = ∫ ψ(a Σ x_i y_i) Φ(x) dν'ⁿ(x) = |a|^(n/2) Φ̂(a y)`.

This is Jacquet's `F_(ψ_a)(Φ)(X) = |a|^(n/2) Φ̂(aX)`. The measure `ν` enters
the relation only through `Φ̂`. Replacing `ν` by `λν` multiplies `Φ̂` by
`λⁿ`, hence the constant `c` of the epsilon monomial by `λⁿ`. So the
self-dual normalization fixes the constant `|a|^(-n²/2)`. With one fixed `ν`
for both characters the factor `|a|^(n/2)` would be missing, and the
constant would be `|a|^(-n(n+1)/2)`.

**The dual integral.** `w_n d w_n = a^r d⁻¹`, so
`W̃_a(g) = W(d w_n ᵗg⁻¹) = W(a^r w_n ᵗ(dg)⁻¹) = ω_π(a)^r W̃(dg)`, and in the
same way `W̃'_a(g) = ω_σ(a)^r W̃'(dg)`. Hence the dual integral for `ψ^a` at
`1 - s` is

`ω^r |a|^(n/2) ∫ W̃(dg) W̃'(dg) Φ̂(a e_n g) |det g|^(1-s) dμ(g)`.

Change `g` to `d⁻¹g`: this gives the factor `κ |det d|^(-(1-s))`. Then change
`g` to `a⁻¹g`, a central translation. `W̃` and `W̃'` transform by
`ω_π⁻¹` and `ω_σ⁻¹`, so this gives `ω |a|^(-n(1-s))`, and `a e_n a⁻¹g = e_n g`.
Altogether the dual integral for `ψ^a` is

`κ ω^n |a|^(n/2 - n(1-s)) |det d|^(-(1-s)) Ψ(1 - s, W̃, W̃', Φ̂)`.

**The epsilon factor.** Divide the dual integral by the integral. The
constant `κ` cancels, and the exponent of `|a|` is

`n/2 - n(1-s) + n(n-1)/2 · (2s - 1) = n²(s - 1/2)`.

The L-polynomials `P` and `P^∨` are unchanged (see the obligations below).
`ζ` is unchanged, too. So the functional equation for `ψ^a` holds with the
monomial `ω^n |a|^(n²(s-1/2)) c X(s)^m`. With `|a|^(n² s) = X(s)^(n² ord a)`
this is `c' X(s)^(m')` with `m' = m + n² ord a` and
`c' = c ω_π(a)^n ω_σ(a)^n |a|^(-n²/2)`, the conclusion of the statement.

**The gamma factor.** With `L(s) = 1 / P(X(s))` and
`L^∨(1 - s) = 1 / P^∨(X(1-s))`, the gamma factor is
`γ(s) = ε(s) P(X(s)) / P^∨(X(1-s))`. The functional equation becomes
`Ψ(1 - s, W̃, W̃', Φ̂) = ζ^(n-1) γ(s) Ψ(s, W, W', Φ)` for the continuations
(`EqualRankGammaEquation`, module `GammaFactor`). Since `P` and `P^∨` do not
change, the statement implies, by the same computation,

`γ(s, π × σ, ψ^a) = ω_π(a)^n ω_σ(a)^n |a|^(n²(s-1/2)) γ(s, π × σ, ψ)`.

This is Jacquet's formula. In integral form,
`Ψ(1 - s, W̃_a, W̃'_a, Φ̂_a) = ζ^(n-1) γ(s, π × σ, ψ^a) Ψ(s, W_a, W'_a, Φ)`.
The gamma formula is not stated in Lean here.

**Derivation obligations.** A proof of the statement must establish:

1. the existence of a compatible quotient measure for `ψ^a`. It does not
   depend on `ψ`, so it is the hypothesis. The nonzero functionals for `ψ^a`
   come from the functional equivalences above;
2. the measure law for every compatible `μ`. It is published
   (`characterChangeCompatibleMeasure`);
3. the uniqueness of self-dual measures and the scaling `ν' = |a|^(1/2) ν`,
   and the Fourier identity `Φ̂_a(y) = |a|^(n/2) Φ̂(ay)` for `IsRowFourierPair`
   with the product measure. Here `Φ̂_a` is again a Schwartz-Bruhat function;
4. the invariance of every compatible quotient measure under the central
   translation `g ↦ a⁻¹g`. This is not published as such;
5. the transport of the rational continuations. Since
   `|det d|^(-s) = X(s)^(-ord(det d))` and `|a|^(-n(1-s)) = X(1-s)^(-n ord a)`,
   the continuations for `ψ^a` are `R_a = κ X^(-ord(det d)) R` and
   `R^∨_a = κ ω^n |a|^(n/2) X^(-(ord(det d) + n ord a)) R^∨`: a nonzero
   constant times a Laurent monomial in `X` times the old ones. Hence the
   generators `P` and `P^∨` of the functional-level spans
   `equalRankRationalValues` and `dualEqualRankRationalValues` are unchanged,
   for every compatible `μ`. The published `EqualRankCharacterChange` and
   `CanonicalCharacterChange` (`zetaSpan_equalRank_characterChange_canonical`,
   `isEqualRankLPolynomial_characterChange_canonical`) prove this for the
   representation-level span `equalRankZetaValues` and the measure
   `unipotentQuotientHaar`. They are reused constructions, and do not prove
   this epsilon assertion or any functional equation;
6. the equality of the monomials as Laurent monomials in `X(s)`, using
   `|a| = q^(-ord a)`. Uniqueness (`IsPadicSymmetricEpsilonFactor.unique`)
   then identifies `e'` with the epsilon factor for `ψ^a`.

## Interpretation

- **Encoding.** With `N = n²` and `|a| = q^(-ord a)`,
  `ω_π(a)^n ω_σ(a)^n |a|^(N(s - 1/2)) · c q^(-ms)` equals
  `c ω_π(a)^n ω_σ(a)^n |a|^(-N/2) · q^(-(m + N ord a)s)`. This is the
  conclusion `e' = (c', m + N ord a)`. The statement asserts that `e'` exists,
  that is, that the pair has an epsilon factor for `ψ^a` and `ν'`.
- **Central characters.** They are hypotheses because the computation moves
  `d` past the long Weyl element, `w_n d w_n = a^r d⁻¹`, and translates by the
  central element `a⁻¹`. Each central character appears with exponent `n`,
  the common rank. The factor is symmetric in `π` and `σ`.
- **Rank one.** For `r = 0`, `n = 1`, the integral is Tate's integral of the
  character `χ = ω_π ω_σ` and the formula is Tate's
  `ε(s, χ, ψ^a) = χ(a) |a|^(s-1/2) ε(s, χ, ψ)` for self-dual measures.
- **Consistency.** The formula has the same shape as the unequal-rank formula
  of `PairFactorCharacterChangeStatement` with `t = r`. It agrees with the
  published `PairEpsilonExponentStatement`: `n(ψ^a) = n(ψ) + ord a`, so `m`
  grows by `n² ord a`. For `a = -1`, `ψ^a = ψ⁻¹`, and the factor is
  `ω_π ω_σ(-1)^n` (Jacquet, p. 8, for gamma).
- **Hypotheses.** `π` and `σ` are irreducible and admissible with given
  central characters. No unramifiedness or conductor condition is assumed,
  and no formula for the change of the factor is a hypothesis. Genericity is
  not assumed. For a pair without nonzero Whittaker functionals no `e`
  satisfies the hypothesis, and the statement holds trivially.
- **Measures.** `ν` and `ν'` are self-dual for `ψ` and `ψ^a`. The
  `SelfDualHaar` type does not assert that self-dual measures exist; the
  statement is about all of them.
- **Field.** `F` is a p-adic field because the canonical topological data and
  the p-adic relations are published only for `PadicField`.
- **Not stated.** The L-polynomial does not change for equal ranks; that
  transport is the published `CanonicalCharacterChange` and is not repeated
  here. The gamma formula and the Archimedean case are not stated.

## Universes

The statement has universe parameters `uF` (the field), `uV` (the space of
`π`) and `uW` (the space of `σ`).

## Lean checks

`lean_check` of the module with declaration
`Langlands.RankinSelberg.EqualRankEpsilonCharacterChangeStatement`:

- 0 errors and 0 warnings.
- The declaration is a definition returning `Prop`, with universe parameters
  `uF`, `uV`, `uW`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
