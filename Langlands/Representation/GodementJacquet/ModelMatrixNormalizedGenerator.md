# Normalized matrix generators on actual Whittaker coefficient models

Author: Worker 468.

The definition `Langlands.GodementJacquet.Padic.modelMatrixLPolynomial` chooses
a polynomial for a full Whittaker-type representation `σ` of `GL(n+1)`.
It uses the canonical data of the supplied p-adic field `F`, the supplied
unitary additive character `ψ`, and the supplied self-dual additive Haar
measure `ν`. The original representation carrier has its own independent
universe. Every natural `n` is allowed, including `n = 0`.

Two specifications describe this choice:

- `modelMatrixLPolynomial_pair` retains the complete
  `IsPadicSymmetricLPolynomial F ψ ν.val σ (rankOneCharacter 1)` certificate.
- `modelMatrixLPolynomial_normalized` says that this same polynomial is an
  `IsMatrixNormalizedGenerator` for `glModelRepresentation ψ n σ ℓ`, for
  every nonzero standard Whittaker functional `ℓ` on the original carrier.

The matrix representation is on the actual coefficient-image subtype
`(glCoefficientModel ψ n σ ℓ).toSubmodule`. The construction does not replace
that image by the original representation or by an irreducible constituent.
The full Whittaker-type hypothesis contains admissibility, finite generation
and a one-dimensional functional space; it includes reducible inputs.

## Extracting the character generator

`RankinSelberg.IsPairLPolynomial.isCharacterLPolynomial` works over a general
field with the topology and measurable structures required by the existing
pair definitions. It extracts the character generator for an arbitrary
scalar character `χ` from a full `IsPairLPolynomial` certificate against
`rankOneCharacter χ`, with the same quotient measure and polynomial.

At `n = 0`, `isPairLPolynomial_self` is precisely the equal-rank character
family. At `n = m+1`, the proof selects block `j = 0`, `k = m`.
Two private equality lemmas identify the transported rank with the pullback
by the identity coordinate relabelling `characterPairRank m`.
`rectangularMeasure_zero_rows` identifies the rectangular product measure
with unit point mass at the zero matrix. The zero-row matrix space is a
singleton, so every set is measurable. Extensionality therefore identifies
its inherited matrix measurable space with the top measurable space
explicitly used in `characterZetaValues`. After these equalities, the
selected normalized-generator assertion is exactly
`IsCharacterLPolynomial`.

## Transport to matrix integrals

`isMatrixNormalizedGenerator_model_of_character` applies the two published
ideal comparisons at the same specified nonzero functional:

```text
zetaSpan (characterZetaValues q ψ abv μ 1 n σ) = jpssI3 F ψ σ ℓ
jpssI2 F ψ σ ℓ = jpssI3 F ψ σ ℓ.
```

These are `RankinSelberg.rankOneMatrixWhittakerComparison` from
`RankOneMatrixWhittakerComparisonProof` and
`GodementJacquet.whittakerModelComparison` from
`WhittakerModelComparisonProof`. Their composition identifies the character
span with the ordinary matrix-coefficient span of the actual model.
The published `RankinSelberg.isNormalizedGenerator_congr` transports the
normalized generator across this equality.

`isMatrixNormalizedGenerator_model_of_pair` begins with a complete symmetric
p-adic pair certificate against the trivial rank-one character.
Since `0 ≤ n`, the existing symmetric-order lemma extracts the ordered
pair certificate. That certificate supplies the subgroup Haar
right-invariance witness and a compatible quotient measure.
Its universal generator clause is specialized at that measure, then the
character extraction and span transport give the matrix generator.
The supplied additive Haar measure is retained in the pair certificate.

## Existence and provenance

`exists_modelMatrixNormalizedGenerator` uses the published
`rankOneCharacter_isOfWhittakerType` for the trivial scalar character and
`symmetricLPolynomialExists` for `(σ, rankOneCharacter 1)`. It obtains one
polynomial with its complete pair certificate before quantifying over `ℓ`.
The preceding transfer proves the generator property for every nonzero
`ℓ`. Classical choice defines `modelMatrixLPolynomial`, and the two
specifications are the corresponding components of its choice theorem.

This is internal support derived from the published definitions and proofs,
not a separate literal literature assertion. The analytic inputs are imported
without modification. In particular, the published `I₂ = I₃` proof
discharges its asymptotic and Mellin interfaces using
`whittakerTypeAsymptotic` and `finiteFunctionMellin`; the pair existence proof
discharges its equal-rank, unequal-rank and common-generator interfaces using
`equalRankAnalytic`, `unequalRankAnalytic` and `unequalRankCommonGenerator`.
No two-block multiplicativity result is used here.

The module constructs normalized generators and retains pair certificates.
It does not construct a common matrix convergence threshold, a matrix
functional equation, dual normalized data, or either closed two-block
gamma/L analytic-base theorem. Those are separate obligations.
