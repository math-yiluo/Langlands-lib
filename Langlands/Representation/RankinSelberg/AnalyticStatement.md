# JPSS convergence and rationality on actual coefficient models

Author: Worker 11. This file defines four proposition targets in namespace
`Langlands.RankinSelberg`:

- `QuotientHaarExistenceStatement`,
- `EqualRankAnalyticStatement`,
- `UnequalRankAnalyticStatement`,
- `UnequalRankCommonGeneratorStatement`.

This module defines the targets. The companion
[QuotientHaarExistence](QuotientHaarExistence.md) proves the first one as
`quotientHaarExistence`. The three analytic targets remain open; downstream
conditional constructions may take them as explicit hypotheses. They restate
parts (i) and (ii) of Theorem 2.7 of Jacquet--Piatetski-Shapiro--Shalika (JPSS),
*Rankin--Selberg convolutions*, Amer. J. Math. 105 (1983), printed pages
390--391, for representations of Whittaker type. The integrals, characters,
coefficient images and Haar measures are the published constructions of
`Whittaker.GeneralLinear`, `Whittaker.Algebraic`,
`RankinSelberg.QuotientIntegrals`, `RankinSelberg.Measures` and
`Analysis.Local.QuotientMeasure`. They are not supplied under new names.

## Common data

Every target fixes a prime `p`, an algebraic `PadicField p` named `F`, and
specified `TopologicalData` `T`. Its topology, valuative relation and local
field structure are installed inside the statement. Positive ranks are
written `n + 1`. JPSS writes `r` for the rank of `π` and `t` for the rank of
`π'`. Here `π` acts on `V` and `σ` on `W`. The two carriers lie in
independent universes `uV` and `uW`.

The topological spaces `GL_{n+1}(F)`, its upper-unipotent subgroup `N` and
the quotient `N \ GL_{n+1}(F)` each receive their Borel measurable structure.
The quotient is `LeftUnipotentQuotient n F`. This is the published left-coset
space `QuotientIntegration.LeftQuotient (upperUnipotent (n + 1) F)`, built
from `QuotientGroup.rightRel`. No normality of `N` is used.

`IsOfWhittakerType n θ π` is the scope of JPSS Section 2.1, printed
pages 385--386. It has three parts.

- `π` is admissible. The published `IsAdmissible` includes smoothness.
- `π` is finitely generated over the group algebra:
  `Module.Finite (MonoidAlgebra ℂ GL_{n+1}(F)) π.asModule`. This is not
  finite-dimensionality over `ℂ`.
- The space `functionals N θ π` of `θ`-equivariant linear functionals is
  linearly equivalent to `ℂ`, that is, it is one-dimensional.

No irreducibility is assumed, so reducible induced representations are
covered. For `π` the character is `standardCharacter ψ n`, namely
`u ↦ ψ(u_{12} + ⋯ + u_{n,n+1})`. For `σ` it is `inverseStandardCharacter ψ n`,
built from the same `ψ`. These are the characters of JPSS, printed page 377,
and the pair condition `W' ∈ W(π'; ψ⁻¹)` of Section 2.4. Each target also
quantifies the actual nonzero functionals `ℓ ∈ glFunctionals ψ n π` and
`ℓ' ∈ glInverseFunctionals ψ n σ`. The Whittaker functions are the elements
of the coefficient images `coefficientModel π ℓ` and `coefficientModel σ ℓ'`,
so `W(g) = ℓ(π(g)v)` for some `v`. This is JPSS's `W(π; ψ)`.

`normalizedAbsoluteValue T` packages `T.normalizedAbs` as an
`AbsoluteValue`. Multiplicativity, nonnegativity, the zero criterion and the
ultrametric inequality are the published results of
`LocalField.Normalization.Proof`. The triangle inequality follows because the
maximum of two nonnegative numbers is at most their sum. Its value is the
existing normalized absolute value, normalized by the residue cardinality
`q = T.residueCardinality`.

The spectral variable is `spectralPoint q s = (q : ℂ) ^ (-s)` from
`RankinSelberg.RationalContinuation`. The proved theorem
`spectralPoint_eq_spectralParameter` identifies it with the shared
`LocalFactor.spectralParameter`, which is `exp(-s log q)`. It specializes
the published `LocalFactor.spectralParameter_eq_cpow` to natural numbers.

## The integrals

The integrals are the published integrals of `RankinSelberg.QuotientIntegrals`.
They are JPSS (2.4), printed pages 387--388.

- Equal rank: `equalRankModelIntegral` is
  `Ψ(s, W, W', Φ) = ∫_{N \ G} W(g) W'(g) Φ(e_{n+1} g) |det g|^s dg`. Here
  `e_{n+1} g` is the last row of `g`, and `Φ` is a Schwartz--Bruhat function
  on `F^{n+1}`.
- Unequal rank: `unequalRankModelIntegral j k` is
  `Ψ(s, W, W'; j) = ∫_{N \ G} ∫_{M(j × (n+1))} W([g,0,0; x,1_j,0; 0,0,1_{k+1}])
  W'(g) |det g|^{s - (r - t)/2} dx dg`. The large rank is
  `n + (j + k + 1) + 1`, so the rank gap is `r - t = j + k + 1`.

The natural numbers `j` and `k` are arbitrary. So every positive rank gap and
every block `0 ≤ j ≤ r - t - 1` occurs, with `k = r - t - 1 - j` as in JPSS.
This includes `j = 0` and rank one. The source's corank-one integral (2.4)(2)
is the case `j = k = 0`. Its printed condition "`r = t - 1`" is a misprint for
`t = r - 1`.

## Measures

The group measures are the published `generalLinearHaar F n`, with
`GL_{n+1}(O)` of mass one, and `unipotentHaar F n`, with `N(O)` of mass one.

A quotient measure `μ` is admissible when it satisfies the published
predicate `QuotientIntegration.IsCompatible N (generalLinearHaar F n)
(unipotentHaar F n) μ`. That predicate requires all of the following.

- `μ` is nonzero and regular.
- `μ` is invariant under right translation by every element of `GL_{n+1}(F)`.
- For every continuous compactly supported complex function `f` on
  `GL_{n+1}(F)`, the average `N g ↦ ∫_N f(u g) du` is `μ`-integrable.
- Its `μ`-integral equals `∫ f dg`.

This is the Weil integration formula. It fixes the scale of `μ`, so `μ` is
the unique quotient measure for these two Haar measures. The averaging
operator descends to the quotient only when the measure on `N` is right
invariant. The published predicate therefore takes the instance
`Measure.IsMulRightInvariant (unipotentHaar F n)`. Each analytic target
retains this explicit instance binder. The companion
[UnipotentUnimodularity](UnipotentUnimodularity.md) proves
`unipotentHaar_rightInvariant` and supplies `unipotentHaar_isMulRightInvariant`
for every natural `n`. Likewise,
[GeneralLinearUnimodularity](GeneralLinearUnimodularity.md) proves
`generalLinearHaarRightInvariant` and supplies
`generalLinearHaar_isMulRightInvariant` for the ambient measure. These results
hold over every nonarchimedean local field with a Borel measurable structure
on the respective group, and preserve the normalized Haar measures above.

`QuotientHaarExistenceStatement n` asserts that `unipotentHaar F n` is right
invariant and that `CompatibleMeasureExists` holds. The latter means that
some quotient measure satisfies `IsCompatible`. No representation or integral
occurs in it. The published
[UnipotentQuotient](UnipotentQuotient.md) constructs `unipotentQuotientHaar`,
proves `unipotentQuotientHaar_isCompatible`, and supplies
`unipotent_compatibleMeasureExists` in every rank over a nonarchimedean local
field, with Borel structures on the ambient group, subgroup and quotient.
Its `unipotentQuotientHaar_unique` identifies every compatible measure with
that construction exactly, for these fixed ambient and subgroup Haar measures.
The companion theorem `quotientHaarExistence` proves
`QuotientHaarExistenceStatement F T n` for every `PadicField F`, every supplied
`TopologicalData T`, and every natural `n`. It installs the topology,
valuation and local-field structure specified by `T` and the three Borel
structures, then uses the constructed measure and proved right invariance;
neither is an additional hypothesis. There is no restriction to canonical
topological data. The analytic targets still quantify over every compatible
`μ`; the measure construction does not prove their analytic conclusions.

The unequal-rank inner integral uses `rectangularMeasure ν j (n + 1)`, the
published product of an arbitrary additive Haar measure `ν` on `F` over the
matrix entries. At zero rows it is the unit point mass. JPSS does not
normalize `dg` or `dx` in parts (i) and (ii). Scaling either measure by a
positive constant scales every integral by that constant. This leaves the
spanned fractional ideal and its normalized generator unchanged. The
self-dual normalization of `ν` enters only in the functional equations of
`FunctionalEquationStatement`.

## Conclusions

`EqualRankAnalyticConclusion` and `UnequalRankAnalyticConclusion` each have
four clauses.

1. Every coefficient-model integral converges absolutely on some right
   half-plane `a < Re s`. `EqualRankConverges` requires integrability on the
   quotient under `μ`. `UnequalRankConverges` requires joint integrability on
   the product of the quotient and the rectangular matrix space under
   `μ.prod ν`, where this analytic target uses
   `ν = rectangularMeasure ν₀ j (n + 1)` for its additive Haar measure `ν₀`
   on `F`. The separately defined iterated Bochner integral does not by itself
   assert joint absolute integrability. The bound `a` may depend on the
   vectors and on `Φ`.
2. Every such integral has a rational continuation: `HasRationalContinuation q
   I R` for some `R ∈ ℂ(X)`. This means `I(s) = R(q^{-s})` with nonzero
   denominator throughout some right half-plane. A pole cannot satisfy it
   through totalized evaluation.
3. The set of all such `R` has a common nonzero Laurent denominator
   (`HasCommonDenominator`). Its `ℂ[X, X⁻¹]`-span is therefore a fractional
   ideal of `ℂ[q^{-s}, q^s]`.
4. That span is generated by `P(X)⁻¹` for a polynomial `P` with `P(0) = 1`
   (`NormalizedGeneratorExists`). JPSS writes `L(s, π × π') = P(q^{-s})⁻¹`.

The value sets `equalRankRationalValues` and `unequalRankRationalValues`
range over the actual model vectors and, in equal rank, all Schwartz--Bruhat
functions. A rational function belongs to the set exactly when it continues
one of these integrals. The published `RationalZeta` module proves that the
normalized generator is unique when it exists. It also proves that a common
denominator makes the span principal. `RationalContinuation` proves that a
rational continuation is unique when `q > 1`.

`UnequalRankCommonGeneratorStatement n r` fixes ranks `t = n + 1 <
r + 1`. It chooses a single polynomial `P` before the block index. Then `P`
is the normalized generator for every `j, k` with `r = n + (j + k + 1)`. This
is the JPSS sentence "there is a similar factor, `L(s, π × π')`, independent
of `j`". The auxiliary `unequalRankValuesAt` only transports the value set
along the equality `r = n + (j + k + 1)` of natural numbers, to match the
fixed large rank with the block-indexed rank.

## Source correspondence

Source: `jpss-1983-rankin-selberg`, file `Jacquet-Piatetski-Shapiro-Shalika--
Rankin-Selberg Convolutions--1983.pdf` in the central library, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. The scan
has no text layer; the following pages were read visually.

- Notation, printed pages 375--378: `N_r`, `K_r = GL_r(O)` and the character
  `ψ(Σ u_{i,i+1})`.
- Section 2.1, pages 385--386: representations of Whittaker type.
- Section 2.4, pages 387--388: the integrals.
- Theorem 2.7(i)--(ii), pages 390--391: absolute convergence of each
  integral "for Re(s) large", rationality in `q^{-s}`, the fractional ideal, and its generator
  `P(q^{-s})⁻¹` with `P(0) = 1`.

JPSS states (i) and (ii) for representations of Whittaker type with arbitrary
Whittaker vectors, which is the scope here. The quotient-measure predicate is
the standard Weil formula, not a numbered JPSS assertion. The functional
equation (iii) is the separate module `FunctionalEquationStatement`.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `EqualRankAnalyticStatement` was inspected: it returns `Prop`,
has universe parameters `uF uV uW`, and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The two other analytic targets have the
same form. `QuotientHaarExistenceStatement` was inspected too: it returns
`Prop`, has the single universe parameter `uF`, and uses the same three axioms. The two lemmas `spectralPoint_eq_spectralParameter` and
`normalizedAbsoluteValue_apply` are proved.
