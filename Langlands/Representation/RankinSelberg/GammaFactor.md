# Gamma factors of pairs as relations

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, defines
when a rational function `G` of `q^{-s}` is the gamma factor
`γ(s, π × σ, ψ) = G(q^{-s})` of a pair. It does this for actual
representations of `GL_{r+1}(F)` and `GL_{n+1}(F)`, `n ≤ r`, and for
supercuspidal isomorphism classes. The module states no theorem target. Every
lemma in it is proved.

No gamma function is chosen. The factor is a relation `IsPairGammaFactor ... G`
on candidate rational functions `G : RationalFunctions` (`RatFunc ℂ`), read at
the published spectral point `spectralPoint q s = q^{-s}`. The module proves
that at most one `G` satisfies the relation and that the relation is invariant
under equivalence of representations. It does not prove that some `G` exists.

## Source

Henniart, *Caractérisation de la correspondance de Langlands locale par les
facteurs ε de paires*, Invent. Math. 113 (1993). Section 1.1 (printed pages
339-340) recalls that Jacquet--Piatetski-Shapiro--Shalika attach to a pair
`(π, τ)` of irreducible admissible representations of `GL_n(F)` and `GL_r(F)`
the factors `L(π × τ, s)`, `ε(π × τ, s, ψ)` and `γ(π × τ, s, ψ)`, the last two
with the Haar measure on `F` self-dual for `ψ`. Section 2.3 (printed page 343)
defines

- (2.3.4) `γ(π × τ, s, ψ) = ε(π × τ, s, ψ) L(π^∨ × τ^∨, 1 - s) / L(π × τ, s)`,

so that the functional equation (2.3.3) of JPSS takes the form

- (2.3.5) `Ψ(1 - s, W̃, W̃') = ω_τ(-1)^r γ(π × τ, s, ψ) Ψ(s, W, W')`.

There `π` is generic on `GL_n(F)`, `τ` is generic on `GL_r(F)` with
`r = n - 1`, `ω_τ` is the central character of `τ`, `W` runs over `W(π, ψ)`,
`W'` over `W(τ, ψ̄)`, and `W̃(g) = W(w_n {}^t g^{-1})`. In Section 3.4
(printed page 347) Henniart applies the same definition (2.3.4) to pairs of
ranks `n` and `r` for every `1 ≤ r ≤ n - 1`.

The functional equations themselves are those of JPSS, *Rankin--Selberg
convolutions*, Amer. J. Math. 105 (1983), Theorem 2.7(iii), printed page 391:
display (1) in equal rank (with a Schwartz--Bruhat function `Φ` and its Fourier
transform `Φ̂`) and display (2) in unequal rank `t ≤ r - 1` (for every block
`j`, with the transformed integral in block `k`, `j + k = r - t - 1`). The sign
is `ω'(-1)^{n-1}` with `n` the rank of the candidate. The published
`FunctionalEquationStatement` and its Markdown spell out both displays.
Substituting (2.3.4) into them gives the displays with `γ` and without
`L`-factors, and this module states those displays directly.

Since `ε = c q^{-ms}`, `L(π × τ, s) = P(q^{-s})^{-1}` and
`L(π^∨ × τ^∨, 1 - s) = Pdual(q^{-(1-s)})^{-1}` for polynomials `P` and `Pdual`,
the gamma factor is `c X^m P(X) / Pdual(q^{-1} X^{-1})` at `X = q^{-s}`: a
rational function of `q^{-s}`. This is why the candidate is an element of
`RatFunc ℂ`. That the relation holds for this rational function, given the
epsilon relation of the published `EpsilonFactor` module, is not proved here.

## The gamma equation for one continuation

`GammaFunctionalEquation q ζ e G R Rdual` says: for every `s` at which
`R(q^{-s})`, `Rdual(q^{-(1-s)})` and `G(q^{-s})` are defined (their
denominators do not vanish),
`Rdual(q^{-(1-s)}) = ζ^e G(q^{-s}) R(q^{-s})`. Here `R` and `Rdual` will be
the rational continuations of an integral and of its transformed integral, and
`ζ^e` is the sign.

`GammaFunctionalEquation.gamma_unique` (proved): for `q > 1`, if a nonzero `R`
satisfies the equation with `G` and with `G'` (same `ζ`, `e` and `Rdual`), then
`G = G'`. Away from finitely many real `t`, all denominators are nonzero at
`s = t` and `R(q^{-t}) ≠ 0`; cancelling gives `G = G'` at infinitely many points
`q^{-t}`, and the published `rationalFunction_eq_of_infinite_eval_eq` applies.
The finiteness lemmas are the published `finite_spectralPoint_roots` and
`finite_reflected_spectralPoint_roots`.

## Fixed-functional gamma equations

The ambient field `F` is a topological field with a measurable structure, and
the quotient `N_{n+1} \ GL_{n+1}(F)` (`LeftUnipotentQuotient n F`) carries a
measurable structure.

`EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G` (ranks `n + 1` and `n + 1`, a
quotient measure `μ`, a functional `ℓ` in `glFunctionals ψ n π` and `ℓ'` in
`glInverseFunctionals ψ n σ`, the functionals for `ψ̄`) says that there is
`ζ : ℂˣ` such that

1. `ζ` is the minus-one scalar of the coefficient model of `σ` (the published
   `HasModelMinusOneScalar`, standing for `ω_σ(-1)`);
2. some element of the published `equalRankRationalValues` is a nonzero
   rational function;
3. for all model vectors `f`, `f'` and every Schwartz--Bruhat `Φ` on
   `F^{n+1}` there are the row Fourier transform `Φhat` of `Φ` for `ψ` and `ν`
   (`IsRowFourierPair`) and rational continuations `R` of
   `equalRankModelIntegral ... f f' Φ` and `Rdual` of
   `dualEqualRankModelIntegral ... f f' Φhat` with
   `GammaFunctionalEquation q ζ n G R Rdual`.

The sign exponent `n` is the candidate rank minus one, as in JPSS.

`UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G` (candidate rank `r + 1`,
test rank `n + 1 < r + 1`) says that there is `ζ` with 1, and for every block
decomposition `r = n + (j + k + 1)`:

2. some element of the published block-`j` values `unequalRankValuesAt j k ...`
   (with the rectangular measure `rectangularMeasure ν j (n + 1)`) is nonzero;
3. for all model vectors `f`, `f'` there are rational continuations `R` of the
   block-`j` integral `unequalRankIntegralAt j k ...` and `Rdual` of the
   published transformed block-`k` integral `dualUnequalRankModelIntegralAt`
   with `GammaFunctionalEquation q ζ r G R Rdual`.

Conjunct 2 is needed because a gamma equation alone does not determine `G`
when every integral vanishes; without it every `G` would satisfy the equation
for such data. It holds in the situation of JPSS: by Theorem 2.7(ii) (printed
pages 390-391) the values span a fractional ideal generated by
`L(s, π × π') = P(q^{-s})^{-1}`, in unequal rank for every block `j` with the
same `P`, so each block has a nonzero value (the published functional-equation
conclusions assert these generators, and the published
`IsNormalizedGenerator.exists_ne_zero` extracts a nonzero value). So
conjunct 2 makes the relation no stronger than the source.

For each of the two equations the module proves:

- `.congr_model`: the equation depends on `ℓ` and `ℓ'` only through their
  coefficient images. In the unequal case the published `unequalRankValuesAt_eq`
  first removes the rank transport.
- `.unique`: for `q > 1` and nonzero `ℓ'`, `G` is unique. The minus-one scalar,
  the Fourier partner and the continuations are unique by published lemmas, a
  nonzero value is supplied by conjunct 2, and `gamma_unique` applies. In
  unequal rank the block `j = 0` is used.
- `.functionalPullback_iff`: pulling both functionals back along equivalences
  (the published `functionalPullback` of `EpsilonFactor`) does not change the
  equation.

## The relations

Here `F` is a nonarchimedean local field (`IsNonarchimedeanLocalField`), and
`GL_{n+1}(F)` and its upper unipotent subgroup carry Borel structures.
`IsEqualRankGammaFactor q ψ abv ν π σ G` is the conjunction of:

1. `Measure.IsMulRightInvariant (unipotentHaar F n)` holds and a compatible
   quotient measure exists (the published `CompatibleMeasureExists`);
2. `π` has a nonzero functional in `glFunctionals ψ n π`;
3. `σ` has a nonzero functional in `glInverseFunctionals ψ n σ`;
4. for every compatible quotient measure `μ` and all nonzero `ℓ`, `ℓ'`,
   `EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G` holds.

`IsUnequalRankGammaFactor hnr q ψ abv ν π σ G` is the same with
`glFunctionals ψ r π` and `UnequalRankGammaEquation`. Only the quotient
measure of the test rank occurs.

`IsPairGammaFactor q ψ abv ν π σ G`, for a candidate `π` of rank `r + 1` and a
test `σ` of rank `n + 1`, is the unequal relation if `n < r`, the equal
relation if `r = n` (after rewriting `π` along `r = n`), and `False` if
`r < n`. This is the dispatch of the published `IsPairEpsilonFactor`.

The design is that of the epsilon relation, for the same reasons. Conjuncts
1--3 make the universal statement 4 non-vacuous, so a missing measure or
functional gives no `G` and never makes two factors agree. Both sides of each
display use the same `μ`, so `γ` does not depend on its scaling, and the
Whittaker model does not depend on which nonzero functional defines it; so
quantifying over every `μ`, `ℓ` and `ℓ'` matches the source, and uniqueness
needs no uniqueness of compatible quotient measures.

The self-duality `IsSelfDual ψ ν` of the additive Haar measure `ν` is not part
of the relations; they define Henniart's gamma factor only when `ν` is
self-dual for `ψ`, and users state that hypothesis. The normalized generators
do not depend on `ν`, so replacing `ν` by `λ ν` (`λ > 0`) changes the gamma
factor as it changes the epsilon factor (see the Markdown of `EpsilonFactor`):
in equal rank `G` becomes `λ^{n+1} G`; in unequal rank block `j` alone would
need `λ^{(k-j)(n+1)} G`, which depends on `j` unless `r = n + 1`, so a single
`G` for all blocks depends on the self-dual normalization; at adjacent ranks
(`r = n + 1`, `j = k = 0`) the relation does not depend on `ν`. These scaling
remarks are not proved in Lean.

Proved lemmas:

- `IsEqualRankGammaFactor.unique`, `IsUnequalRankGammaFactor.unique`,
  `IsPairGammaFactor.unique`: for `q > 1`, two rational functions satisfying
  the relation are equal.
- `.of_equiv` and `.congr_equiv` for all three: for equivalences `π ≃ π₂` and
  `σ ≃ σ₂` the relations agree.
- `isPairGammaFactor_of_lt`, `isPairGammaFactor_self` and
  `not_isPairGammaFactor_of_lt` unfold the case split.

## p-adic fields and supercuspidal classes

`IsPadicPairGammaFactor F ψ ν π σ G` is for a p-adic field `F : PadicField p`
with its canonical topological data and actual representations `π` of
`GL_{r+1}(F)` and `σ` of `GL_{n+1}(F)`. It installs the canonical topology,
valuative relation and local-field structure and the Borel structures, as the
published targets do, and is `IsPairGammaFactor` with `q` the residue
cardinality `F.canonicalTopologicalData.residueCardinality` and the published
`normalizedAbsoluteValue`. `IsPadicPairGammaFactor.unique` (using the
published `residueCardinality_gt_one`) and `IsPadicPairGammaFactor.congr_equiv`
are proved.

`IsClassGammaFactor F ψ ν π τ G` lifts `IsPadicPairGammaFactor` to classes `π`
in the published `PadicField.SupercuspidalClass F (r + 1)` (carriers in
universe `uV`) and `τ` in `PadicField.SupercuspidalClass F (n + 1)` (carriers in
universe `uW`). The lift is well defined by `congr_equiv` and the published
`SmoothRep.equivOfIso`. `isClassGammaFactor_mk` (on representatives it is the
p-adic pair relation, `Iff.rfl`) and `IsClassGammaFactor.unique` are proved.

The relations do not assume genericity; without nonzero functionals no `G`
satisfies them.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `IsClassGammaFactor` was inspected: it returns `Prop`, has
universe parameters `uF uV uW`, and uses only `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry` and no new axiom.
