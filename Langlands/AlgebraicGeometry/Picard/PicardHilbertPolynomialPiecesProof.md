# The Hilbert-polynomial pieces of the Picard functor (proof)

The module `Langlands.AlgebraicGeometry.Picard.PicardHilbertPolynomialPiecesProof` proves

```lean
theorem picardHilbertPolynomialPieces : PicardHilbertPolynomialPiecesStatement.{u}
```

The statement is the open decomposition of the Picard functor of a projective flat family with
geometrically integral fibres over a noetherian ring into Hilbert-polynomial pieces. It follows
S. L. Kleiman, *The Picard scheme*, pp.28–30 (literature id
`kleiman-2005-picard-scheme-arxiv-math0504020v1`).

## Proof

The theorem applies the helper theorem `picardHilbertPolynomialPiecesReduction` (module
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPolynomialPiecesReduction`, with its own Markdown).
That theorem derives the statement from four statements on fibre cohomology. Each of these has a
separate proof:

- `ProperFlatFibreCohomologySemicontinuityStatement`, proved by
  `Modules.properFlatFibreCohomologySemicontinuity`;
- `ProperFibreCohomologyDimBaseChangeStatement`, proved by
  `Modules.properFibreCohomologyDimBaseChange`;
- `ProjectiveFibreTwistCohomologyStatement`, proved by `Modules.projectiveFibreTwistCohomology`;
- `ProjectiveRelativeDivisorFibreHilbertStatement`, proved by
  `Modules.projectiveRelativeDivisorFibreHilbert`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
