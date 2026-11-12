# Proof of the generic classification-to-integral epsilon comparison

Author: Worker 4933. This module, in namespace `Langlands.RankinSelberg`,
proves

```
theorem genericLanglandsPairEpsilonFactorComparison :
    GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uV, uW}
```

with the three universe parameters independent. The statement and its
conventions are documented in `GenericLanglandsPairEpsilonFactorComparisonStatement.md`;
this module does not change it or any relation it uses. The helper lemmas are
in the namespace `Langlands.RankinSelberg.GenericEpsilonComparison`.

## What is proved

For a p-adic field `F`, a unitary additive character `ψ`, a Haar measure `ν`
self-dual for `ψ`, and generic `π` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)`
(carriers in `max uF uV` and `max uF uW`): every `e` with
`IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν.val π σ e` satisfies
`IsPadicSymmetricEpsilonFactor F ψ ν.val π.representation σ.representation e`.
No further hypothesis is used: no factor comparison, Whittaker-model comparison
or existence premise, and no restriction to supercuspidal or square-integrable
pairs.

## Mathematical idea

Write `π = J(ξ)` and `σ = J(η)`, where `ξ` and `η` are the normalized parabolic
inductions of the square-integrable blocks `τ_i` and `μ_j` of presenting
Langlands data. Then:

1. Gamma multiplicativity (JPSS 1983, Theorem (3.1)) in both block families
   gives `γ(ξ × η) = ∏ γ(τ_i × μ_j)`.
2. Each gamma factor has the form `ε · L(1 − s, dual)/L(s)` with its own
   epsilon factor. So
   `ε(ξ × η) · L^∨(ξ × η)/L(ξ × η) = ∏ ε(τ_i × μ_j) · ∏ L^∨(τ_i × μ_j)/∏ L(τ_i × μ_j)`.
3. `L(ξ × η) = ∏ L(τ_i × μ_j)` (JPSS (9.4), displays (3) and (4), through the
   published L-factor results). The dual L-polynomials need not be compared:
   after cancelling the common L-factor, each side is an epsilon monomial
   `c q^(-ms)` divided by a dual L-polynomial evaluated at `q^(-(1-s))`, and
   every dual L-polynomial has constant term one. Comparing lowest-order terms
   in `q^(-s)` forces the two epsilon monomials to agree:
   `ε(ξ × η) = ∏ ε(τ_i × μ_j)`, which is the classification value `e`.
4. `π` and `σ` are quotients of `ξ` and `η` with the same Whittaker functionals,
   so the functional equation of `ξ × η` is the functional equation of
   `π × σ`, and `e` is the epsilon factor of `π × σ` (JPSS (3.3) and (9.4)).

This is the route that Henniart 2002, §2.8 (printed page 596), refers to for
the product formula `ε(s, π × π') = ∏ ε(s, π_i × π'_j, ψ)`.

## The Lean proof

### Rational cancellation

- `monomial_mul_eq_of_coeff_zero`: in `RatFunc ℂ`, if
  `a X^k D = a' X^k' D'` with `a, a' ≠ 0` and polynomials `D, D'` of constant
  term `1`, then `k = k'` and `a = a'`. Multiplying by `X^N` for
  `N = |k| + |k'|` gives a polynomial identity
  `C a X^(k+N) D = C a' X^(k'+N) D'`. If the exponents differ, cancelling the
  smaller power of `X` and reading the constant coefficient gives `a = 0` or
  `a' = 0`. If they agree, cancelling and reading the constant coefficient gives
  `a = a'`.
- The published `Langlands.RankinSelberg.rationalGammaExpression_cancel` from
  `Langlands/Correspondence/SegmentEpsilonAlgebra.lean`: if
  `rationalGammaExpression δ c m P D = rationalGammaExpression δ c' m' P D'`
  with `P ≠ 0` and `D, D'` of constant term `1`, then `c = c'` and `m = m'`.
  The proof applies the reflection substitution `X ↦ δ/X`
  (`LocalFactor.RationalReflection.subst`, an involution by `subst_subst`), which
  turns the reflected dual polynomials back into `D`, `D'`, cancels the common
  nonzero factor coming from `P`, and applies its general `monomial_mul_cancel` lemma to
  `(c δ^m) X^(-m) D' = (c' δ^m') X^(-m') D`.

### Two block families

`isPadicSymmetricEpsilonFactor_normalizedProduct` treats block families of the
shape `succBlockShape m hm` and `succBlockShape n hn`, blocks of Whittaker type
for the standard character. Its hypotheses are an L-polynomial `∏ i, ∏ j, Q i j`
of the two inductions (`IsPadicSymmetricLPolynomial`), block L-polynomials
`Q i j`, and block epsilon factors `b i j`. Its conclusion is that
`epsilonFactorProduct b` is the symmetric epsilon factor of the two
inductions. The proof:

- `normalizedProductWhittakerType` gives Whittaker type of the inductions, and
  `TemperedLFactorGamma.epsilon_exists_of_whittakerType` some epsilon factor
  `e₀` of the inductions;
- `TemperedLFactorDual.nonempty_dualTwoFamilyLPolynomialData` gives dual
  L-polynomials (`ψ.scale (-1)`, inverse-transpose pullbacks) of the inductions
  and of every block pair;
- `TemperedLFactorGamma.gamma_doubleProduct` (published `gammaMultiplicativity`
  in both families) gives block gamma factors `G i j` whose product is a gamma
  factor of the inductions;
- `symmetricGammaExpression` (with `whittakerTypeGammaConstructionInput`)
  rewrites each `G i j` and the product as `rationalGammaExpression` of the
  certified epsilon, L- and dual L-data;
- `TemperedLFactorGamma.rationalGammaExpression_prod` turns the product of the
  block expressions into the expression of `epsilonFactorProduct b`,
  `∏ Q` and `∏ D_ij`;
- `rationalGammaExpression_cancel` concludes `epsilonFactorProduct b = e₀`.
  Here `∏ Q ≠ 0` because an L-polynomial has constant term one
  (`coeff_zero`), and both dual polynomials have constant term one for the same
  reason.

`isPadicSymmetricEpsilonFactor_normalizedProduct_of_blocks` restates this for
arbitrary `BlockShape`s whose blocks are irreducible, admissible and have a
nonzero Whittaker functional: block sizes are written as successors and the
blocks are of Whittaker type by `isOfWhittakerType_of_isGeneric`.
Its block hypotheses are the forms used by `IsSquareIntegrableDataEpsilonFactor`:
`IsPadicRankLPolynomial` and `IsPadicRankEpsilonFactor`.

### Passing to quotients

`isEqualRankEpsilonFactor_of_surjective`, `isUnequalRankEpsilonFactor_of_surjective`,
`isPairEpsilonFactor_of_surjective`, `isPadicPairEpsilonFactor_of_surjective`
and `isPadicSymmetricEpsilonFactor_of_surjective` show: if `f : π → π₂` and
`g : σ → σ₂` are surjective intertwiners and `π₂`, `σ₂` have nonzero functionals
of the required kinds, then an epsilon factor of `(π, σ)` is one of
`(π₂, σ₂)`. A functional `ℓ₂` of `π₂` pulls back to the nonzero functional
`functionalsComap f hf ℓ₂` of `π` (`functionalsComap_ne_zero`) with the same
coefficient model (`coefficientModel_functionalsComap`), so the functional
equation for `π` transfers by `EqualRankEpsilonEquation.congr_model` (resp.
`UnequalRankEpsilonEquation.congr_model`). The pair version splits by rank
order with `isPairEpsilonFactor_of_lt`, `isPairEpsilonFactor_self` and
`not_isPairEpsilonFactor_of_lt`; the p-adic versions supply the canonical
topology and Borel measurable structures; the symmetric version splits on the
rank order of `IsPadicSymmetricEpsilonFactor`.

### Square-integrable blocks

`hasFunctional_of_essentiallySquareIntegrable`: an irreducible essentially
square-integrable block `A : SmoothRep.{0, uF, uV}` of positive rank has a
nonzero Whittaker functional for the entrywise character of `ψ`, in every
carrier universe `uV`. The published `essentiallySquareIntegrable_isGeneric`
is stated for carriers in `max uF uV`, so the proof applies it to
`SmoothRep.universeLift A`, transfers irreducibility and essential
square-integrability along `SmoothRep.universeLiftEquiv`, and pulls the
functional back along that equivalence (`functionalPullback`,
`functionalPullback_ne_zero`).

### Main theorem

`genericLanglandsPairEpsilonFactorComparison` unfolds the certificate `he` into
presenting square-integrable data `d`, `d'` and the universal block-product
clause. Applied to `d`, `d'`, that clause gives block epsilon factors `b` with
`e = epsilonFactorProduct b`. Then:

1. `squareIntegrableDataLFactor` gives `P` and block L-polynomials `Q` with
   `IsLanglandsPairLPolynomial … P` and `P = ∏ i, ∏ j, Q i j`. Unfolding the
   former gives tempered data `dt`, `et` presenting `π`, `σ` and the
   L-polynomial `P` of their standard modules.
2. `genericLanglandsQuotientLFactor` at `dt`, `et` gives `P'`, an L-polynomial
   of the standard modules and also `IsPadicSymmetricLPolynomial` of `π`, `σ`
   themselves; uniqueness of the L-polynomial (`unique`) gives `P' = P`.
3. The surjections `f`, `g` of `d.IsLanglandsQuotient π` and
   `d'.IsLanglandsQuotient σ` come from the normalized inductions `ξ`, `η` of the
   blocks of `d`, `d'`. These are of Whittaker type by
   `normalizedProduct_isOfWhittakerType_of_blocks` and
   `hasFunctional_of_essentiallySquareIntegrable`. Since `π`, `σ` are generic,
   `whittakerSet_eq_of_surjective_of_whittakerType` and
   `inverseWhittakerSet_eq_of_surjective_of_whittakerType` identify the
   Whittaker sets of `ξ`, `η` with those of `π`, `σ`, and
   `isPadicSymmetricLPolynomial_congr_whittakerSets` turns step 2 into
   `IsPadicSymmetricLPolynomial … ξ η (∏ i, ∏ j, Q i j)`.
4. `isPadicSymmetricEpsilonFactor_normalizedProduct_of_blocks` gives that
   `epsilonFactorProduct b = e` is the symmetric epsilon factor of `(ξ, η)`.
5. `isPadicSymmetricEpsilonFactor_of_surjective` along `f`, `g` passes it to
   `(π, σ)`. The required nonzero functionals of `π`, `σ` for the standard
   character are the third conjunct of `IsGeneric`, and those for the inverse
   character come from `isOfInverseWhittakerType_of_isGeneric`.

The measure `ν` is used only through `ν.val` and its self-duality, exactly as
in the statement; `ψ` is the same in every step.

## Sources

- G. Henniart, *Une caractérisation de la correspondance de Langlands locale
  pour GL(n)*, Bull. Soc. Math. France 130 (2002), 587-602
  (`henniart-2002-characterization`), §2.8, printed page 596: the product
  formula for `ε(s, π × π')` over the blocks of the Langlands data.
- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
  convolutions*, Amer. J. Math. 105 (1983) (`jpss-1983-rankin-selberg`):
  Theorem (3.1) (gamma multiplicativity), Remark (3.3) (Whittaker quotients),
  Proposition (9.4), displays (3) and (4), and Theorem (9.5) (L-factors of
  Langlands quotients and of square-integrable data). The Lean proof uses these
  only through the published Library theorems named above.

The cancellation of step 3 of the mathematical idea, through the constant term
of the dual L-polynomials, uses the published rational-function algebra; it replaces a separate
comparison of dual L-polynomials.

## Lean checks

`lean_check` of `Langlands.Representation.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonProof`
in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiles with 0 errors
and 0 warnings. The module uses no `sorry`, `admit` or new axioms.
