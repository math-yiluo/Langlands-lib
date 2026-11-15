# Assembly of the Picard scheme of an integral-fibre family over a noetherian ring

Authors: Worker 5705, with the first theorem taken from Worker 5656.

Worker 5705 wrote this helper module for Task 5705 (`07219dde-fd87-48cf-83be-db16cbb3707c`).
It composes published results. The proof of the Task 5705 target
(`NoetherianIntegralFibrePicardSheafAFSchemeProof`) applies its last theorem. It contains no
`sorry` and no new axioms. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.
It does not use `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement` or any other
statement excluded by the Task 5705 contract, and its import closure contains none of them.

## Theorems

All are in the namespace `Langlands.AlgebraicGeometry.Picard`.

- `noetherianIntegralFibrePicardSheafAFScheme_of_noetherianAffineTests`:
  `NoetherianIntegralFibrePicardNoetherianTestsStatement.{u}` implies
  `NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}`. Given `R`, `f`, the section and
  the ample line bundle, the hypothesis gives `P` over `Spec R`, locally of finite presentation
  with finite affine neighbourhoods, and an isomorphism `α` between the functor of points of `P`
  and the fppf Picard class sheaf, both restricted to affine noetherian tests. The Library
  theorem `NoetherianAffineTests.nonempty_representableBy_of_noetherianAffine` (module
  `NoetherianAffineTestsPicardExtension`, by Worker 5656) turns `α` and the section into a
  representation of `RelativePicard.classSheafPresheaf f` on the whole slice by the same `P`.
  This theorem is the same as Worker 5656's
  `noetherianIntegralFibrePicardSheafAFScheme_of_noetherianTests` in the Task 5656 draft
  (module `NoetherianIntegralFibrePicardNoetherianTestsReduction`). It has a different name and
  lives in a module that does not import
  `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeIntegralFibreReduction`. This avoids a name
  clash if both modules are published, and keeps the excluded statements out of the import
  closure.
- `noetherianIntegralFibrePicardNoetherianTests_of_piecesRepresentability`:
  `PicardHilbertPiecesRepresentabilityStatement.{u}` implies
  `NoetherianIntegralFibrePicardNoetherianTestsStatement.{u}`. It applies the published
  reduction `noetherianIntegralFibrePicardPiecesReduction`
  (`NoetherianIntegralFibrePicardPiecesReductionStatement`) to the hypothesis and to the
  published proofs of its other four hypotheses:
  - `properAmpleClosedImmersionBySections` (`ProperAmpleClosedImmersionBySectionsStatement`);
  - `picardHilbertPolynomialPieces` (`PicardHilbertPolynomialPiecesStatement`);
  - `properFlatIntegralSheafClassTwist` (`ProperFlatIntegralSheafClassTwistStatement`);
  - `noetherianOpenPiecesGluing` (`NoetherianOpenPiecesGluingStatement`).
- `noetherianIntegralFibrePicardSheafAFScheme_of_piecesRepresentability`:
  `PicardHilbertPiecesRepresentabilityStatement.{u}` implies
  `NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}`. This is the composition of the
  two previous theorems.

## Sources

The mathematics is Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`), Theorem 4.8 and its proof. The steps are
in the Markdown of the statements and proofs named above.
