# Existence of symmetric p-adic L-polynomials

Author: Worker 364.

The module defines the closed proposition
`Langlands.RankinSelberg.SymmetricLPolynomialExistenceStatement.{uF,uV,uW}`.
It states existence of the published symmetric L-polynomial relation for every
pair of actual representations of Whittaker type. It contains no proof of that
proposition and assumes no analytic statement or prior factor existence.

## Exact statement

The proposition universally quantifies over a natural number `p` with
`Fact p.Prime`, a `PadicField.{uF} p` called `F`, using the fixed canonical data
`F.canonicalTopologicalData`. It then quantifies over:

- `ψ : UnitaryAdditiveCharacter F.Carrier` for the canonical topology; this
  structure already includes continuity, unit-circle values and nontriviality;
- a supplied `ν : LocalFactor.PadicAbelian.SelfDualHaar
  F.canonicalTopologicalData ψ`, whose underlying additive Haar measure is
  `ν.val`;
- `r n : ℕ`, giving all positive ranks `r + 1` and `n + 1`;
- independent complex module carriers `V : Type uV` and `W : Type uW`, each
  with `AddCommGroup` and `Module ℂ` instances;
- actual representations `π` of `GL_(r+1)(F)` on `V` and `σ` of
  `GL_(n+1)(F)` on `W`.

Assume `IsOfWhittakerType r (standardCharacter ψ r) π` and
`IsOfWhittakerType n (standardCharacter ψ n) σ`, both under the canonical
topology. The conclusion is

```text
∃ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P.
```

`IsOfWhittakerType` is the existing conjunction of admissibility, finite
generation over the group algebra, and a linear equivalence of the indicated
Whittaker-functional space with `ℂ`. It permits reducible representations.
There is no irreducibility assumption and no equality between `uV` and `uW`.
The statement is conditional on the supplied self-dual measure; it does not
assert existence of that measure. Although L-polynomial existence needs less
normalization, this target uses the self-dual measure interface needed by its
factor consumers.

## One polynomial for every compatible quotient measure

The conclusion uses `IsPadicSymmetricLPolynomial` unchanged. For `n ≤ r` it
means `IsPadicPairLPolynomial F ψ ν.val π σ P`; for `r < n` it means the
same relation for `(σ, π)`. In equal rank it keeps the given order. Thus no
rank order is excluded.

For the selected order, `IsPadicPairLPolynomial` includes both the existence
of a right-invariance witness for the fixed unipotent Haar measure together
with a compatible quotient measure, and the assertion that **every**
right-invariance witness and every quotient measure compatible with the fixed
ambient and subgroup Haar measures gives `IsPairLPolynomial` for this same
`P`. Its `q` is the canonical residue cardinality and its absolute value is
`normalizedAbsoluteValue F.canonicalTopologicalData`.

That pair relation says that `P(0) = 1` and `1/P` generates the Laurent span
of the actual zeta values: equal-rank values when the ranks coincide, and the
values of every block when they differ. The existential choice of `P` lies
outside the universal measure quantifiers. Establishing only
`∀ μ, ∃ P, ...` would not prove this target.

## Source and derived provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.

Theorem 2.7(i)–(ii), printed pages 390–391, states convergence and rationality
and the normalized reciprocal-polynomial generator for representations of
Whittaker type. In unequal rank the generator is independent of the block
index. Section 2.12, printed page 403, extends the L-factor notation to the
opposite rank order by exchanging the pair; it also discusses character
independence and equal-rank symmetry. The present target uses the existing
rank-order convention and does not separately assert those latter identities.
These original pages were read visually. No JPSS-specific erratum was found
in the checked project and Library note filenames or literature index.

This is a derived packaging of those source results using the Library's
canonical p-adic data, Haar compatibility relation and character transport,
rather than a new analytic theorem. The source's ranks `r,t` correspond to
the selected larger and smaller successor ranks here. Its second Whittaker
model uses the inverse character, whereas both hypotheses here use the
standard character; the bridge below accounts for this difference.

## Later proof bridge and outstanding dependencies

A later proof must combine the following existing interfaces.

1. Split into `n < r`, `n = r` and `r < n`, exchanging the representations
   and their independent carrier universes in the last case.
2. Transfer the Whittaker-type hypothesis of the selected second
   representation to `inverseStandardCharacter ψ`. The published
   `Whittaker.characterChangeFunctionalEquiv` at `-1`, together with
   `RankinSelberg.standardCharacter_scale_neg_one`, gives the required linear
   equivalence of functional spaces. Admissibility and finite generation
   are unchanged. This transfers the one-dimensionality clause for the
   same representation; it does not require irreducibility.
3. Use `quotientHaarExistence`, or
   `unipotentHaar_isMulRightInvariant` and
   `unipotent_compatibleMeasureExists`, at the canonical topological data.
   These measure-existence results are already proved.
4. At the canonical `unipotentQuotientHaar`, apply
   `EqualRankAnalyticStatement.pairLPolynomialExists` in equal rank.
   In unequal rank apply
   `UnequalRankCommonGeneratorStatement.pairLPolynomialExists`, supplying
   `UnequalRankAnalyticStatement` for every block
   `r = n + (j + k + 1)` in the selected order. These theorems are proved
   conditional bridges in `PairLFactor`; their analytic hypotheses are
   substantive remaining inputs.
5. Choose the resulting polynomial once. The already proved
   `unipotentQuotientHaar_unique` identifies every compatible measure for
   the fixed Haar normalizations with the canonical measure, so that the
   same polynomial works for all of them. An alternative route may use
   `isPairLPolynomial_smul_measure` with its finite positive scalar and
   sigma-finiteness hypotheses, after proving the required scalar
   comparison. Separate per-measure existence without such a transfer is
   insufficient.
6. Package the measure-existence conjunct and universal measure clause,
   and unfold the symmetric relation in the selected rank order.

The open analytic inputs are `EqualRankAnalyticStatement`,
`UnequalRankAnalyticStatement` for all relevant blocks, and
`UnequalRankCommonGeneratorStatement`. They include actual half-plane
convergence, rational continuation, denominator control, normalized-generator
existence and agreement across unequal-rank blocks. Their existing proof
tasks are respectively `5998b0b2-e367-4e85-8d4d-47e3b9b4a222`,
`b01bbdd0-5321-41f4-908e-2048e837da34`, and
`13326f3a-e77f-4ed1-a44a-b6407f6b7c0a`. This statement neither proves nor
assumes them. Functional equations, epsilon/gamma-factor existence and
Langlands classification are not needed for this L-existence bridge.
