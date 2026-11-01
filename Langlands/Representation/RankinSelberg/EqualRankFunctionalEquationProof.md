# Equal-rank normalized functional equation

Author: Worker 216.

The theorem `Langlands.RankinSelberg.equalRankFunctionalEquation` proves exactly
`Langlands.RankinSelberg.EqualRankFunctionalEquationStatement.{uF,uV,uW} F T n`
from `Langlands.Representation.RankinSelberg.FunctionalEquationStatement`. This
is JPSS 1983, Theorem 2.7(iii), for equal ranks `n+1 = n+1` (printed p.391). The
binders are any prime `p`, any p-adic field `F`, supplied topological data `T`,
and any `n : ℕ`, so every positive rank is covered. The field and the two
representation-carrier universes stay independent. There are no hypotheses
beyond the target.

The proof assembles published Library theorems and adds nothing to them:

- `equalRankGammaExistence`, from
  `Langlands.Representation.RankinSelberg.EqualRankGammaExistenceProof`, gives
  one rational gamma comparison `G` for the supplied data;
- `equalRankAnalytic`, from
  `Langlands.Representation.RankinSelberg.EqualRankAnalyticProof`, gives the
  normalized generators;
- `HarmonicAnalysis.rowFourierCompatibility`, from
  `Langlands.HarmonicAnalysis.RowFourierCompatibilityProof`, gives row Fourier
  closure and inversion for a self-dual measure;
- `gammaNormalization_of_incidence`, from
  `Langlands.Representation.RankinSelberg.GammaNormalizationAlgebra`, divides a
  gamma equation by the two generators and produces the epsilon monomial.

## Provenance

JPSS 1983, §2.10 (printed p.396), proves Theorem 2.7(iii) in two steps. First,
the two zeta integrals have a ratio `γ(s)` that does not depend on the data.
Then, by §2.9 (printed p.395), dividing `γ` by the L-factors leaves a monomial.
Gamma existence is the first step and the normalization theorem is the second.
The Fourier surjectivity lemma below is elementary and does not appear in the
source, which uses without comment that the Fourier transform is a bijection on
Schwartz–Bruhat functions.

## `exists_isRowFourierPair_of_selfDual`

Hypotheses: `RowFourierClosed ψ ν d` and `IsRowSelfDual ψ ν d`. Conclusion:
every test function `Ψ` is the row Fourier partner of some `Φ`. By closure, take
`Ψ₁ = F Ψ`, `Ψ₂ = F Ψ₁` and `Φ = F Ψ₂`. Inversion, used once for `Ψ₂` and once
for `Ψ`, gives `F Φ (y) = Ψ₂(-y) = F Ψ₁ (-y) = Ψ(y)`.

## `equalRankConclusion_of_gammaEquation`

The setting is generic: a topological field `F` with `1 < q`, representations
`π` and `σ` of `GL_(n+1)(F)`, functionals `ℓ` and `ℓ'`, a quotient measure `μ`
and an additive Haar measure `ν`. The hypotheses are row Fourier closure and
inversion in dimension `n+1`, `EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G`, a
normalized generator `P` of `equalRankRationalValues` and a normalized generator
`Pdual` of `dualEqualRankRationalValues`. The conclusion is
`EqualRankFunctionalEquationConclusion q ψ abv μ ν π σ ℓ ℓ'`.

Proof. The gamma equation provides `ζ` and the model-minus-one scalar statement.
For each `(f, f', Φ)` it also provides a Fourier partner `Φhat` and
continuations `R` and `Rdual` with `GammaFunctionalEquation q ζ n G R Rdual`.
The proof then checks the two incidence hypotheses of
`gammaNormalization_of_incidence`:

- An original value `R` from data `(f, f', Φ)` is paired with the dual value of
  `(f, f', Φhat)`, because rational continuations are unique when `1 < q`.
- A dual value from `(f, f', Ψ)` comes, by the surjectivity lemma, from some `Φ`
  whose Fourier partner is `Ψ`. Fourier partners and continuations are unique,
  so the gamma equation for `Φ` pairs this dual value with an original value.

The normalization theorem returns a unit `c` and an integer `m`, and the
conclusion is witnessed by `ζ, c, m, P, Pdual`. The scalar `ζ` comes from `G`,
while `c` and `m` depend only on `G`, the two value sets and the generators.
All of them are therefore fixed before any coefficient vector or test function
is chosen. For each data, the theorem uses the Fourier partner and the
continuations from the gamma equation. The equation it gets is
`NormalizedFunctionalEquation q P Pdual ζ c n m R Rdual`, whose rational
continuation domain is the one in the target.

## `equalRankFunctionalEquation`

The proof first obtains `equalRankGammaExistence F T n` and
`equalRankAnalytic F T n`. It then introduces the target's binder instances,
together with second countability. The nonarchimedean instance is the
published `equalRankGamma_valuative_nonarchimedean`. That class is Prop-valued,
so it agrees definitionally with the private copy in the target module. After
the target's binders are introduced:

- `T.residueCardinality_gt_one` gives `1 < q`.
- `rowFourierCompatibility ψ ν (n + 1)`, applied to the self-duality of `ν`,
  gives closure and inversion in dimension `n+1`.
- Gamma existence gives `G` with `EqualRankGammaEquation`.
- The analytic theorem, applied to `(π, σ, ℓ, ℓ')`, gives `P`.
- Applied to the inverse-transpose pair with character `ψ.scale (-1)` and the
  dual functionals, the analytic theorem gives `Pdual`. The Whittaker-type and
  nonvanishing hypotheses come from `isOfWhittakerType_firstDual`,
  `isOfWhittakerType_secondDual`, `firstDualFunctional_ne_zero` and
  `secondDualFunctional_ne_zero`. `dualEqualRankRationalValues_eq` identifies
  these values with `dualEqualRankRationalValues`.

The generic theorem then gives the conclusion.
