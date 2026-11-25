# Proof: relative effective divisors with H-quasi-projective Hilbert-polynomial pieces

This module proves the published proposition
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement`
(input (a) of the Picard reduction `PicardHilbertPiecesRepresentabilityReductionStatement`).

The main theorem is

```lean
theorem Langlands.AlgebraicGeometry.Picard.relativeEffectiveDivisorHilbertPieces :
    RelativeEffectiveDivisorHilbertPiecesStatement.{u}
```

Its type is the target proposition exactly, for an arbitrary universe `u`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof is a single application of three published Library theorems:

- the reduction
  `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReduction.relativeEffectiveDivisorHilbertPiecesReduction :
  RelativeEffectiveDivisorHilbertPiecesReductionStatement.{u}`, which is the
  implication
  `HilbertSchemeUniversalFamilyStatement.{u} → RelativeEffectiveCartierLocusStatement.{u} →
  RelativeEffectiveDivisorHilbertPiecesStatement.{u}`;
- `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily :
  HilbertSchemeUniversalFamilyStatement.{u}`: the Hilbert scheme of a
  projective flat family over a noetherian ring, on all test schemes, with
  its universal closed subscheme and H-projective Hilbert-polynomial pieces;
- `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocus.relativeEffectiveCartierLocus :
  RelativeEffectiveCartierLocusStatement.{u}`: the relative effective Cartier
  locus of a flat closed subscheme of a proper flat family over a locally
  noetherian base is open, and is the universal locus over which the ideal is
  relative effective Cartier.

The theorem is the reduction applied to the other two. The mathematical
route is the one recorded in the Markdown of those modules: Kleiman,
*The Picard scheme* (arXiv math/0504020v1), Theorem 3.7 and its proof
(pp.23–24), with the quasi-projectivity of the pieces taken from the proof of
Theorem 4.8 (p.30).

## Dependencies

Only the three Library modules imported by this file:
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReductionProof`,
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusProof` and
`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof`.
