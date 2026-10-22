# JPSS functional equations on actual coefficient images

Author: Worker 11. This file defines three proposition targets in namespace
`Langlands.RankinSelberg`:

- `EqualRankFunctionalEquationStatement n`,
- `UnequalRankFunctionalEquationStatement n r`,
- `Theorem27Statement`, the whole of JPSS Theorem 2.7 (see "The family statement").

None is proved, and none is assumed anywhere. The first two restate Theorem
2.7(iii), displays (1) and (2), of Jacquet--Piatetski-Shapiro--Shalika (JPSS),
*Rankin--Selberg convolutions*, Amer. J. Math. 105 (1983), printed page 391.
The common data, the scope `IsOfWhittakerType`, the integrals, the quotient
measure and the absolute value are those of `AnalyticStatement`; see its
Markdown. Representations `π` of `GL_{r+1}(F)` and `σ` of `GL_{n+1}(F)`
correspond to JPSS's `π` on `G_r` and `π'` on `G_t`. In equal rank `r = n`.

## The source statement

JPSS, Theorem 2.7(iii), printed page 391, reads as follows. Let `π`, `π'` be
of Whittaker type on `G_r`, `G_t`, with `W ∈ W(π; ψ)` and `W' ∈ W(π'; ψ̄)`.

- If `r = t`, there is a factor `ε(s, π × π', ψ)` of the form `c q^{-ns}`
  such that

  `Ψ(1-s, W̃, W̃', Φ̂) / L(1-s, π^ι × π'^ι)
    = ω_{π'}(-1)^{r-1} ε(s, π × π', ψ) Ψ(s, W, W', Φ) / L(s, π × π')`.

- If `t ≤ r - 1`, set `k = r - t - 1 - j`. Then

  `Ψ(1-s, ρ(w_{r,t}) W̃, W̃'; k) / L(1-s, π^ι × π'^ι)
    = ω_{π'}(-1)^{r-1} ε(s, π × π', ψ) Ψ(s, W, W'; j) / L(s, π × π')`,

  the factor `ε` being independent of `j`.

Here `W̃(g) = W(w_r ᵗg⁻¹)`, with `w_r` the long Weyl element; this is
(2.1)(4), printed page 386, where `W̃ ∈ W(π^ι; ψ̄)`. Also
`w_{r,t} = diag(1_t, w_{r-t})`, and `ρ` is right translation. The
representation `π^ι` is `g ↦ π(ᵗg⁻¹)`. `Φ̂` is the Fourier transform
`Φ̂(y) = ∫ Φ(x) ψ(Σ x_i y_i) dx` with the self-dual measure for `ψ`. JPSS,
Section 0, printed page 378, writes `∫ Φ(y) ψ(tr(ᵗy x)) dy` with `dy`
"self-invariant". The `L` factors are the normalized generators
of Theorem 2.7(ii).

## Dual data

The character `ψ̄ = ψ⁻¹` is the published `ψ.scale (-1)`, that is,
`x ↦ ψ(-x)`, from `HarmonicAnalysis.CharacterTransport`. Two lemmas relate it
to the published unipotent characters:

- `standardCharacter_scale` proves that the standard character of
  `ψ.scale a` is the published `scaledStandardCharacter ψ a`.
- `standardCharacter_scale_neg_one` and `inverseStandardCharacter_scale_neg_one`
  prove that for `ψ.scale (-1)` the standard and inverse characters exchange.
  They use the published `scaledStandardCharacter_neg_one`.

The function transform is the published `dualFunction n`, namely
`f ↦ (g ↦ f(w ᵗg⁻¹))`. By the published `dualFunction_mem` and
`dualFunction_inverse_mem` it reverses the covariance character.

- `firstDualFunction ψ n W` is `W̃`. It lies in the Whittaker functions for
  `ψ.scale (-1)`, so `W̃ ∈ W(π^ι; ψ̄)`.
- `secondDualFunction ψ n W'` is `W̃'`. It lies in the inverse Whittaker
  functions for `ψ.scale (-1)`, so `W̃' ∈ W(π'^ι; ψ)`.
- `translateWhittaker ψ n W a` is `ρ(a)W`, `g ↦ W(g a)`. Right translation
  keeps the covariance condition.
- `blockWeylAt n r` is the actual matrix `diag(I_{n+1}, w_{r-n})` in
  `GL_{r+1}(F)`. This is `w_{r+1, n+1}` in JPSS's notation. The reindexing only
  identifies `(n + 1) + (r - n)` with `r + 1`.

The published `dualFunction_coefficient` shows that `W̃` is a coefficient of
`inverseTransposePullback π`, the representation `π^ι`, for a transported
nonzero functional. So the transformed functions form the model of `π^ι`.
This module does not identify `π^ι` with the contragredient of `π`.

## The central sign

JPSS writes `ω_{π'}(-1)`, but defines the central character `ω_π` only for
irreducible `π` (Section 0, printed page 378). A representation of Whittaker
type may be reducible and need not act by scalars on its carrier. Its centre
still acts on the Whittaker model by scalars. For central `z`, the functional
`ℓ ∘ π(z)` is again equivariant, so it is a multiple of `ℓ` by the
one-dimensionality hypothesis. `HasModelMinusOneScalar σ ℓ' ζ` states that every
function `f` in the coefficient image of `σ` satisfies `f(-g) = ζ f(g)`. For
irreducible `σ` this `ζ` is `ω_σ(-1)`. The proved theorem
`HasModelMinusOneScalar.unique` shows that `ζ` is unique when `ℓ'` is nonzero:
evaluate a nonzero coefficient at the identity. The source exponent is "large
rank minus one", so the sign is `ζ^n` in equal rank `n + 1` and `ζ^r` in
unequal rank, with large rank `r + 1`.

## The equation

`epsilonMonomial q c m s = c (q^{-s})^m` with `c ∈ ℂˣ` and `m ∈ ℤ`. This is
JPSS's form `c q^{-ns}`. `epsilonMonomial_ne_zero` proves that it is nonzero
for positive `q`.

`NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual` is the equation

`Pdual(q^{-(1-s)}) Rdual(q^{-(1-s)}) = ζ^e · c (q^{-s})^m · P(q^{-s}) R(q^{-s})`

for every complex `s` at which both rational functions have nonzero
denominators. `R` continues the original integral and `Rdual` the dual
integral. Multiplying by `P` is dividing by `L(s) = P(q^{-s})⁻¹`. Multiplying
by `Pdual` is dividing by `L(1-s, π^ι × π'^ι) = Pdual(q^{-(1-s)})⁻¹`. Using
rational continuations avoids evaluating an integral outside its region of
convergence.

## Equal rank

`dualEqualRankModelIntegral` is the published `equalRankIntegral` for
`ψ.scale (-1)` applied to `W̃`, `W̃'` and a test function, with the same
quotient measure and absolute value. `dualEqualRankRationalValues` is the set
of rational continuations of these integrals over all model vectors and all
Schwartz--Bruhat functions.

`EqualRankFunctionalEquationConclusion` asserts that there are `ζ`, `c`, `m`,
`P` and `Pdual`, chosen before any vector or test function, such that:

- `ζ` is the minus-one scalar of the model of `σ`;
- `P` is the normalized generator of the original values, that is, `L(s, π × σ)`;
- `Pdual` is the normalized generator of the dual values, that is,
  `L(s, π^ι × σ^ι)`;
- for all model vectors and every `Φ` there are a Schwartz--Bruhat `Φ̂` with
  `IsRowFourierPair ψ ν Φ Φ̂` and continuations `R`, `Rdual` of
  `Ψ(s, W, W', Φ)` and `Ψ(s, W̃, W̃', Φ̂)` satisfying
  `NormalizedFunctionalEquation` with sign exponent `n`.

`IsRowFourierPair` is the published plus-sign transform for the product of `ν`
over the row coordinates. It determines `Φ̂` uniquely.

## Unequal rank

`unequalRankIntegralAt j k hr` transports the published `unequalRankIntegral`
along the natural-number equality `hr : r = n + (j + k + 1)`.
`dualUnequalRankModelIntegralAt` is the dual integral of display (2). It uses
block `k`, character `ψ.scale (-1)`, the function `ρ(w_{r+1,n+1}) W̃` and
`W̃'`. `dualUnequalRankRationalValuesAt` is the set of its rational
continuations over all model vectors.

`UnequalRankFunctionalEquationConclusion` quantifies `ζ`, `c`, `m`, `P` and
`Pdual` before the block indices. Then for every `j, k` with
`r = n + (j + k + 1)`:

- `P` is the normalized generator of the block-`j` original values;
- `Pdual` is the normalized generator of the block-`k` dual values;
- for all model vectors there are continuations `R`, `Rdual` satisfying
  `NormalizedFunctionalEquation` with sign exponent `r`.

So the epsilon factor and both `L` factors are independent of `j`, as in the
source. Every block `0 ≤ j ≤ r - n - 1` occurs.

## Measures

The p-adic statements quantify every additive character `ψ`, every compatible
quotient measure `μ` (as in `AnalyticStatement`, including the
`Measure.IsMulRightInvariant (unipotentHaar F n)` binder), and every additive
Haar measure `ν` on `F` with `IsSelfDual ψ ν`. The same `ν` gives the row
Fourier transform and both rectangular measures `rectangularMeasure ν j` and
`rectangularMeasure ν k`. JPSS uses the self-dual measure `dx` throughout.
The normalization matters: if `dx` were scaled by `λ`, the two sides of (2)
would change by `λ^{j(n+1)}` and `λ^{k(n+1)}`, and `ε` would depend on `j`.
The existence of a self-dual measure is the separate published proposition
`SelfDualMeasureExists ψ`. The existence of a compatible quotient measure is
`QuotientHaarExistenceStatement`. Neither is assumed.

## Other details

The statements install the Borel structures and the valuation topology of `F`.
The private lemma `valuative_nonarchimedean` derives the additive
nonarchimedean structure from the valuative topology, using Mathlib's
open-submodule basis. It is needed for the published `IsSelfDual`. No
hypothesis is added to the targets. The two carriers keep independent
universes `uV` and `uW`, and every rank one and every positive rank gap occurs.

## The family statement

`Theorem27Statement` quantifies every prime `p`, every `PadicField p` named `F`
and every `TopologicalData` `T`. It is the conjunction of:

- `EqualRankAnalyticStatement F T n` for every `n`;
- `UnequalRankAnalyticStatement F T n j k` for every `n`, `j`, `k`;
- `UnequalRankCommonGeneratorStatement F T n r` for every `n`, `r`;
- `EqualRankFunctionalEquationStatement F T n` for every `n`;
- `UnequalRankFunctionalEquationStatement F T n r` for every `n`, `r`.

The first three are from `AnalyticStatement`. So this is Theorem 2.7, parts
(i)--(iii), in every pair of positive ranks, with carriers in the universes
`uV` and `uW`. `QuotientHaarExistenceStatement` is not part of it, because it
is not an assertion of Theorem 2.7.

## Source correspondence

Source: `jpss-1983-rankin-selberg`, file `Jacquet-Piatetski-Shapiro-Shalika--
Rankin-Selberg Convolutions--1983.pdf` in the central library, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. The scan
has no text layer; the pages were read visually.

- Section 0, printed pages 377--378: the characters, the plus-sign Fourier
  transform with self-dual measure, and the central character of an
  irreducible representation.
- Section 2.1, pages 385--386: scope, `W(π; ψ)` and `W̃` in display (4).
- Section 2.4, pages 387--388: the integrals.
- Theorem 2.7(iii), page 391: displays (1) and (2) and the sentence "the
  factor `ε(s, π × π', ψ)` being independent of `j`". The exponent `r - 1` of
  `ω_{π'}(-1)` uses the rank `r` of `π`, the larger rank.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `UnequalRankFunctionalEquationStatement` and `Theorem27Statement`
were inspected: each returns `Prop`, has universe parameters `uF uV uW`, and
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. The
equal-rank target has the same form. The character lemmas, `translateWhittaker_apply`, the dual-function
evaluation lemmas, `HasModelMinusOneScalar.unique` and
`epsilonMonomial_ne_zero` are proved.
