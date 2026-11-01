# Proof of equal-rank rank-one extension reverse L-divisibility

Author: Worker 719.

This module proves the published proposition
`Langlands.RankinSelberg.EqualRankRankOneExtensionLDivisibilityStatement.{uF,uV,uW}`
from `Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionDivisibilityStatement`
as the closed theorem

```lean
theorem Langlands.RankinSelberg.equalRankRankOneExtensionLDivisibility :
    EqualRankRankOneExtensionLDivisibilityStatement.{uF, uV, uW}
```

with independent universe parameters `uF`, `uV`, `uW` and no hypotheses.

The proof uses three published theorems. `symmetricLPolynomialExists`
(module `SymmetricLPolynomialExistenceProof`) gives existence of symmetric
p-adic L-polynomials; it is used at the base carrier universe `uW` and at the
induced carrier universe `max uF uW`. `equalRankRankOneExtensionSpanComparison`
(module `EqualRankRankOneExtensionSpanComparisonProof`) gives the equal-rank
Laurent-span comparison. `normalizedProductWhittakerType` (module
`NormalizedProductWhittakerTypeProof`) gives the Whittaker type of normalized
products in successor block shapes.
The proof uses only the standard axioms. It does not import
`TwoBlockLConditionalAssembly`, any L-multiplicativity theorem, or the
section 9.3 tail theorem. Its import closure contains the statement module
`MultiplicativityStatement`, which only defines propositions and is imported
by `NormalizedProductWhittakerTypeStatement`.

## Whittaker type of the induced representation

`NormalizedProductWhittakerTypeStatement` is stated for shapes
`succBlockShape m h`, with blocks of ranks `m i + 1`. The endpoint's induced
representation uses `twoBlocks 1 (t + 1) …` with `pairFamily χlift σ₁`.

- `equalRankExtensionRanks t = ![0, t]`, with
  `equalRankExtensionRankSum t : ∑ i, (![0, t] i + 1) = (1 + t) + 1`.
- `equalRankExtensionFamily χrep σ₁`: the blocks `(χrep, σ₁)` indexed by
  `Fin 2`, at the ranks `![0, t] i + 1`, on the carriers `pairCarrier C W i`.
- `isOfWhittakerType_equalRankExtension F ψ χrep σ₁ hχ hσ`: if
  `χrep` and `σ₁` are of Whittaker type (ranks `1` and `t + 1`), then
  `canonicalNormalizedProductInduced (twoBlocks 1 (t + 1) …) (pairFamily χrep σ₁)`
  is of Whittaker type for `standardCharacter ψ (1 + t)`.

The two shapes have equal rank functions only pointwise (`0 + 1` against
`1`), so the families cannot be compared directly. The proof packs each
(shape, family) pair into one element of the sigma type of rank functions
`s` (positive, summing to `(1 + t) + 1`) together with families at the ranks
`s i`. The two packed pairs are equal: the rank functions agree by `funext`
and `fin_cases`, and the families agree heterogeneously block by block. The
Whittaker-type predicate is a function on this sigma type. Rewriting along
the equality turns the goal into the `succBlockShape` instance, which
`normalizedProductWhittakerType` proves from the blockwise Whittaker types.

## Final theorem

Fix the statement's data and hypotheses `hπ` (Whittaker type of `π`) and `hσ`
(Whittaker type of `σ₁`).

1. `χlift` is of Whittaker type. The published
   `rankOneCharacter_isOfWhittakerType` covers `rankOneCharacter χ` on `ℂ`.
   `IsOfWhittakerType.of_equiv` transports it along `conjULiftEquiv` (from the
   span-comparison module) to the conjugated representation on
   `ULift.{uW} ℂ`.
2. The induced representation `I` is of Whittaker type, by
   `isOfWhittakerType_equalRankExtension`.
3. `symmetricLPolynomialExists.{uF, uV, uW}` (ranks `t + 1`, `t`) gives
   `Pbase` with `IsPadicSymmetricLPolynomial F ψ ν π σ₁ Pbase`.
   `symmetricLPolynomialExists.{uF, uV, max uF uW}` (ranks `t + 1`, `1 + t`;
   the carrier of `I` lives in `Type (max uF uW)`) gives `Pind` with
   `IsPadicSymmetricLPolynomial F ψ ν π I Pind`. These are the first two
   conclusions.
4. Divisibility. Since `t ≤ t + 1` and `1 + t ≤ t + 1`, the published
   `isPadicSymmetricLPolynomial_of_le` unfolds both to
   `IsPadicPairLPolynomial`. Each supplies a compatible quotient measure
   (`μb` in rank `t`, `μi` in rank `1 + t`) and the pair L-polynomial property
   for it.
   - Base, ranks `t < t + 1`: `isPairLPolynomial_of_lt` at `j = k = 0` says
     that `Pbase` is the normalized generator of the block zeta values
     `unequalRankZetaValuesAt 0 0 rfl … μb (rectangularMeasure ν 0 (t + 1)) π σ₁`.
   - Induced, ranks `1 + t` and `t + 1`: unfolding `IsPairLPolynomial`, the
     branch `1 + t < t + 1` is false and the equal-rank branch holds by
     `hrn : t + 1 = 1 + t`. So `Pind` is the normalized generator of
     `equalRankZetaValues … μi (hrn ▸ π) I`.

   The published span comparison `equalRankRankOneExtensionSpanComparison`
   with `μb`, `μi` and `hrn` gives inclusion of the
   base span in the induced span. The third conjunct of the published
   `laurentPolynomialDivisibility` (`NormalizedGeneratorSpanDivisibilityStatement`)
   turns the inclusion into `Pbase ∣ Pind`.

## Relation to the source

The statement is an internal prerequisite for the general-rank descent of
JPSS (1983) section 7.2, beyond the rank range of Lemma (5.5); see the
statement Markdown. This module adds only the formal assembly. The analytic
content is in the span comparison, whose proof Markdown describes the route
through Proposition 9.1 and the last-row reduction of printed page 449.
