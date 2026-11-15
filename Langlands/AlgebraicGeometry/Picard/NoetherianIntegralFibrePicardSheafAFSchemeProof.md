# The Picard scheme of an integral-fibre family over a noetherian ring (proof)

Authors: Worker 5705, with Worker 22 and Worker 5656. The proofs composed here are by Worker
5705 and Worker 22, as listed below. Worker 5656 wrote the first theorem of the helper module
`NoetherianIntegralFibrePicardSheafAFSchemeAssembly`.

The module `Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeProof`
proves

```lean
theorem noetherianIntegralFibrePicardSheafAFScheme :
    NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}
```

This is the target of Task 5705 (`07219dde-fd87-48cf-83be-db16cbb3707c`). Let `R` be a
noetherian ring and `f : X ⟶ Spec R` proper and flat with geometrically integral fibres, with a
section, such that `X` has an ample line bundle. Then the fppf Picard class sheaf of `f` is
represented by a scheme `P` over `Spec R` in which every finite set of points lies in an affine
open subscheme. This is S. L. Kleiman, *The Picard scheme*, Theorem 4.8(2) (literature id
`kleiman-2005-picard-scheme-arxiv-math0504020v1`).

## Proof

The theorem is a single term. Apart from the helper module
`Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeAssembly`, which is
submitted with it, every theorem it uses is already published in the Library. All names below
are in the namespace `Langlands.AlgebraicGeometry` or its sub-namespaces.

1. The effective quotient by a flat proper equivalence relation
   (`FlatProperEquivalenceRelationQuotientStatement`; Altman–Kleiman, Nitsure, Theorem 6.8).
   `FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme` (module
   `FlatProperEquivalenceRelationQuotientReductionProof`, Worker 5705) proves
   `FlatProperEquivalenceRelationQuotientReductionStatement`: the Hilbert scheme with its
   universal family implies the quotient statement. It is applied to
   `HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily` (module
   `HilbertSchemeUniversalFamilyProof`, Worker 22), the proof of
   `HilbertSchemeUniversalFamilyStatement`.
2. Quotients of fppf sheaves on locally noetherian tests
   (`FppfQuotientLocallyNoetherianStatement`).
   `FppfQuotientLocallyNoetherianReduction.fppfQuotientLocallyNoetherianReduction` (module
   `FppfQuotientLocallyNoetherianReductionProof`, Worker 22) proves
   `FppfQuotientLocallyNoetherianReductionStatement`: the quotient statement of step 1 implies
   this statement. It is applied to the term of step 1.
3. Representability of the Hilbert-polynomial pieces of the Picard sheaf
   (`PicardHilbertPiecesRepresentabilityStatement`).
   `PicardHilbertPiecesReduction.picardHilbertPiecesRepresentabilityReduction` (module
   `Picard.PicardHilbertPiecesRepresentabilityReductionProof`, Worker 22) proves
   `PicardHilbertPiecesRepresentabilityReductionStatement`. It has four hypotheses, given in
   this order:
   - `Picard.relativeEffectiveDivisorHilbertPieces` (Worker 22), the proof of
     `RelativeEffectiveDivisorHilbertPiecesStatement`;
   - `Picard.properFlatIntegralLinearSystem` (Worker 5705), the proof of
     `ProperFlatIntegralLinearSystemStatement`;
   - the term of step 2, for `FppfQuotientLocallyNoetherianStatement`;
   - `Picard.RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange`
     (Worker 5705), the proof of `RelativeEffectiveDivisorBaseChangeStatement`.
4. The target. The helper theorem
   `Picard.noetherianIntegralFibrePicardSheafAFScheme_of_piecesRepresentability` is applied to
   the term of step 3. Its Markdown describes it. In two steps, it
   - applies the published reduction `noetherianIntegralFibrePicardPiecesReduction`, with the
     published proofs `properAmpleClosedImmersionBySections`,
     `picardHilbertPolynomialPieces`, `properFlatIntegralSheafClassTwist` and
     `noetherianOpenPiecesGluing` of its other four hypotheses, to obtain representability on
     noetherian affine tests (`NoetherianIntegralFibrePicardNoetherianTestsStatement`);
   - passes to all tests, using the section of `f`, with Worker 5656's
     `NoetherianAffineTests.nonempty_representableBy_of_noetherianAffine`.

Steps 1 to 3 are written out inline. The Library has no single theorem yet for
`FlatProperEquivalenceRelationQuotientStatement`, `FppfQuotientLocallyNoetherianStatement` or
`PicardHilbertPiecesRepresentabilityStatement`. Compositions of steps 1 to 3 have been
submitted separately, and this proof does not depend on them.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It does not use
`AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement` or any other statement excluded by the
Task 5705 contract, and its import closure contains none of them.
