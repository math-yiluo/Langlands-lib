# The Picard scheme of an integral-fibre family over a noetherian ring (proof)

The module `Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeProof`
proves

```lean
theorem noetherianIntegralFibrePicardSheafAFScheme :
    NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}
```

Let `R` be a
noetherian ring and `f : X ⟶ Spec R` proper and flat with geometrically integral fibres, with a
section, such that `X` has an ample line bundle. Then the fppf Picard class sheaf of `f` is
represented by a scheme `P` over `Spec R` in which every finite set of points lies in an affine
open subscheme. This is S. L. Kleiman, *The Picard scheme*, Theorem 4.8(2) (literature id
`kleiman-2005-picard-scheme-arxiv-math0504020v1`).

## Proof

The theorem is a single term. Apart from the helper module
`Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeAssembly`, every
theorem it uses is published elsewhere in the Library. All names below
are in the namespace `Langlands.AlgebraicGeometry` or its sub-namespaces.

1. The effective quotient by a flat proper equivalence relation
   (`FlatProperEquivalenceRelationQuotientStatement`; Altman–Kleiman, Nitsure, Theorem 6.8).
   `FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme` (module
   `FlatProperEquivalenceRelationQuotientReductionProof`) proves
   `FlatProperEquivalenceRelationQuotientReductionStatement`: the Hilbert scheme with its
   universal family implies the quotient statement. It is applied to
   `HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily` (module
   `HilbertSchemeUniversalFamilyProof`), the proof of
   `HilbertSchemeUniversalFamilyStatement`.
2. Quotients of fppf sheaves on locally noetherian tests
   (`FppfQuotientLocallyNoetherianStatement`).
   `FppfQuotientLocallyNoetherianReduction.fppfQuotientLocallyNoetherianReduction` (module
   `FppfQuotientLocallyNoetherianReductionProof`) proves
   `FppfQuotientLocallyNoetherianReductionStatement`: the quotient statement of step 1 implies
   this statement. It is applied to the term of step 1.
3. Representability of the Hilbert-polynomial pieces of the Picard sheaf
   (`PicardHilbertPiecesRepresentabilityStatement`).
   `PicardHilbertPiecesReduction.picardHilbertPiecesRepresentabilityReduction` (module
   `Picard.PicardHilbertPiecesRepresentabilityReductionProof`) proves
   `PicardHilbertPiecesRepresentabilityReductionStatement`. It has four hypotheses, given in
   this order:
   - `Picard.relativeEffectiveDivisorHilbertPieces`, the proof of
     `RelativeEffectiveDivisorHilbertPiecesStatement`;
   - `Picard.properFlatIntegralLinearSystem`, the proof of
     `ProperFlatIntegralLinearSystemStatement`;
   - the term of step 2, for `FppfQuotientLocallyNoetherianStatement`;
   - `Picard.RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange`,
     the proof of `RelativeEffectiveDivisorBaseChangeStatement`.
4. The target. The helper theorem
   `Picard.noetherianIntegralFibrePicardSheafAFScheme_of_piecesRepresentability` is applied to
   the term of step 3. Its Markdown describes it. In two steps, it
   - applies the published reduction `noetherianIntegralFibrePicardPiecesReduction`, with the
     published proofs `properAmpleClosedImmersionBySections`,
     `picardHilbertPolynomialPieces`, `properFlatIntegralSheafClassTwist` and
     `noetherianOpenPiecesGluing` of its other four hypotheses, to obtain representability on
     noetherian affine tests (`NoetherianIntegralFibrePicardNoetherianTestsStatement`);
   - passes to all tests, using the section of `f`, with
     `NoetherianAffineTests.nonempty_representableBy_of_noetherianAffine` (module
     `NoetherianAffineTestsPicardExtension`).

Steps 1 to 3 are written out inline. The Library also proves
`FlatProperEquivalenceRelationQuotientStatement`, `FppfQuotientLocallyNoetherianStatement` and
`PicardHilbertPiecesRepresentabilityStatement` as single theorems composing the same steps
(`flatProperEquivalenceRelationQuotient`, module `FlatProperEquivalenceRelationQuotientProof`;
`fppfQuotientLocallyNoetherian`, module `FppfQuotientLocallyNoetherianProof`;
`Picard.picardHilbertPiecesRepresentability`, module
`Picard.PicardHilbertPiecesRepresentabilityProof`), and this proof does not depend on them.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It does not use
`AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement`, which the Library derives from the
statement proved here, and its import closure contains no module of the normal finite-type
abelian statements.
