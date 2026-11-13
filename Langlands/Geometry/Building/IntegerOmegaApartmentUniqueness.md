# Uniqueness of integer-valued omega-compatible apartment classes

This module proves the uniqueness conclusion of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Proposition 6.2.6, printed p.216
(PDF p.247), for an integer-valued valuation on an arbitrary field. The
registered *Corrections and additions* (2024), Chapter 6, p.32, do not change
this proposition.

For a connected reductive group `G`, an actual maximal split torus `i`, an
integer-valued valuation `v`, and the same actual `CentralizerDatum i`, two full
`KPApartmentData` classes satisfying `IntegerValuation.IsOmegaCompatible` are
equal. No local-field, characteristic, valuation nontriviality or
opposite-factor-pair hypothesis is added. The field has arbitrary universe.

## Implemented proof and published inputs

`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus` uses the following
published Library results:

- `Langlands.GroupScheme.rootRankOneFactorization`, imported from
  `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`, gives actual
  rank-one factorization for every nonidentity rational root-group point of a
  connected reductive group with an actual maximal split torus. Its first
  component supplies an actual opposite factor pair.
- `IntegerValuation.IsOmegaCompatible.eq_of_hasOppositeFactorPairs`, imported
  from `Langlands.Geometry.Building.IntegerOmegaApartmentRigidity`, identifies
  the two full classes once these pairs exist.

The latter theorem implements the comparison argument of Proposition 6.2.6:
integer-valued V 6 gives common centralizer displacements; finite Weyl-quotient
averaging constructs an equivariant affine comparison with identity derivative;
the opposite-pair reflection displacement formula identifies all nonidentity
root values, and hence the classes. This module discharges its opposite-pair
premise by the independently published rank-one theorem.

`IntegerOmegaCompatibleApartmentUniquenessStatement.{u}` is the Prop-valued
bundle of this assertion, and `integerOmegaCompatibleApartmentUniqueness` proves
it. This is an internal adapter of existing published proofs, rather than a
new construction of root valuations.

## Use over a maximal unramified extension

The field in this assertion need not be a nonarchimedean local field.
Consequently it applies to the maximal unramified extension with its
integer-valued valuation, if both classes satisfy full V 6 for the same actual
centralizer and maximal split torus.

The assertion compares classes for the same torus. It does not construct a
special torus, an integral model or a special apartment containing a prescribed
Galois-fixed building point. Comparisons between different tori still require
the published transport hypotheses.

## Sources

- Kaletha–Prasad (2023), Proposition 6.2.6, printed p.216 / PDF p.247; registered
  source `kaletha-prasad-2023-bruhat-tits-new-approach`.
- Kaletha–Prasad (2024), *Corrections and additions*, Chapter 6, p.32; registered
  source `kaletha-prasad-2024-corrections`.
