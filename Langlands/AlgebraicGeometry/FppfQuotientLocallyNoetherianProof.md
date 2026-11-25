# Proof: representability on locally noetherian tests of fppf sheaves presented by a flat proper equivalence relation

This module proves the
published proposition
`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianStatement`
(input (c'') of the Picard reduction `PicardHilbertPiecesRepresentabilityReductionStatement`).

The main theorem is

```lean
theorem Langlands.AlgebraicGeometry.fppfQuotientLocallyNoetherian :
    FppfQuotientLocallyNoetherianStatement.{u}
```

Its type is the target proposition exactly, for an arbitrary universe `u`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof is a single term built from three published Library theorems:

- `Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReduction.fppfQuotientLocallyNoetherianReduction :
  FppfQuotientLocallyNoetherianReductionStatement.{u}`, which is the implication
  `FlatProperEquivalenceRelationQuotientStatement.{u} → FppfQuotientLocallyNoetherianStatement.{u}`;
- `Langlands.AlgebraicGeometry.FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme :
  FlatProperEquivalenceRelationQuotientReductionStatement.{u}`, which is the
  implication
  `HilbertSchemeUniversalFamilyStatement.{u} → FlatProperEquivalenceRelationQuotientStatement.{u}`
  (the proof of Nitsure's Theorem 6.8 from the Hilbert scheme, in
  `FlatProperEquivalenceRelationQuotientReductionProof`);
- `Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily :
  HilbertSchemeUniversalFamilyStatement.{u}`: the Hilbert scheme of a
  projective flat family over a noetherian ring, on all test schemes, with its
  universal closed subscheme and H-projective Hilbert-polynomial pieces.

Applying the second theorem to the third gives the effective quotient theorem
`FlatProperEquivalenceRelationQuotientStatement.{u}`, and applying the first
theorem to that gives the target. The mathematical route is the one recorded
in the Markdown of those modules. The quotient comes from N. Nitsure,
*Construction of Hilbert and Quot schemes*
(`nitsure-2005-hilbert-quot-arxiv-math0504590v1`), Theorem 6.8 (p.33). The
sheaf is then identified with the quotient on locally noetherian tests as in
S. L. Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`), Lemma 4.9 and its proof
(pp.30–31), with the fppf topology in place of the étale one.

## Dependencies

Only the three Library modules imported by this file:
`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionProof`,
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof` and
`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof`.
