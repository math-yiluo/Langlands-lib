# Proof: quasi-projective representability of the Hilbert-polynomial pieces of the Picard sheaf

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705),
by agreement with that task's first executor, Worker 5705. It proves the
published proposition
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityStatement`
(the statement of Task 6214, which records that this proof is done under
Task 5705). The operator's answer to request
`98389b48910e54088e0e2b2ba6aaad9c` allows such prerequisite proofs to stay
under Task 5705.

The main theorem is

```lean
theorem Langlands.AlgebraicGeometry.Picard.picardHilbertPiecesRepresentability :
    PicardHilbertPiecesRepresentabilityStatement.{u}
```

Its type is the target proposition exactly, for an arbitrary universe `u`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof is a single term. Its head is the published reduction

- `Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction.picardHilbertPiecesRepresentabilityReduction :
  PicardHilbertPiecesRepresentabilityReductionStatement.{u}`, which is the
  implication
  `RelativeEffectiveDivisorHilbertPiecesStatement.{u} →
  ProperFlatIntegralLinearSystemStatement.{u} →
  FppfQuotientLocallyNoetherianStatement.{u} →
  RelativeEffectiveDivisorBaseChangeStatement.{u} →
  PicardHilbertPiecesRepresentabilityStatement.{u}`.

Its four inputs are supplied by published Library theorems:

1. `Langlands.AlgebraicGeometry.Picard.relativeEffectiveDivisorHilbertPieces :
   RelativeEffectiveDivisorHilbertPiecesStatement.{u}`: the scheme of relative
   effective divisors with H-quasi-projective Hilbert-polynomial pieces
   (Kleiman, Theorem 3.7);
2. `Langlands.AlgebraicGeometry.Picard.properFlatIntegralLinearSystem :
   ProperFlatIntegralLinearSystemStatement.{u}`: the linear system of an
   invertible module on a proper flat family with integral fibres (Worker 5705);
3. the term
   `FppfQuotientLocallyNoetherianReduction.fppfQuotientLocallyNoetherianReduction
   (FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme
   HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily) :
   FppfQuotientLocallyNoetherianStatement.{u}`. It applies the published reduction
   from the effective quotient theorem (`FlatProperEquivalenceRelationQuotientStatement`)
   to the published proof of that theorem from the Hilbert scheme. This is the
   same term that proves `Langlands.AlgebraicGeometry.fppfQuotientLocallyNoetherian`
   in the separately submitted module
   `Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianProof`. It is
   written out here so that this proof depends only on published modules;
4. `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange :
   RelativeEffectiveDivisorBaseChangeStatement.{u}`: arbitrary base change of
   relative effective Cartier divisors (Worker 5705).

The mathematical route is the one recorded in the Markdown of the reduction
module `PicardHilbertPiecesRepresentabilityReductionProof`: Kleiman, *The
Picard scheme* (arXiv math/0504020v1), proof of Theorem 4.8 (pp.29–31). Each
piece of the Picard sheaf is the quotient of an open part of the divisor
scheme by the linear-system equivalence relation.

## Dependencies

Only the seven Library modules imported by this file:
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionProof`,
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesProof`,
`Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`,
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof`,
`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionProof`,
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof` and
`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof`.
