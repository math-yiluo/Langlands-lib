# The highest left cuspidal derivative lemma for `GL_n`: proof

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivativeProof`.

`Langlands.Classification.LeftCuspidalDerivative.leftCuspidalDerivativeLemma` proves the
Library proposition
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma.{uF, uV}`
(module `Langlands.Representation.Classification.LeftCuspidalDerivativeStatement`). It
adds no hypotheses and uses only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). The theorem only assembles the five clauses. Each clause is proved in a
helper module under `Langlands/Representation/Classification/LeftCuspidalDerivative/`.

1. **Subquotients.** `leftReduced_of_isSubquotient` (module `Basic`): a subquotient of a
   subquotient is a subquotient, so this follows from the definition of `LeftReduced`. No
   finite-length hypothesis is used.
2. **Products.** `leftReduced_binaryProduct` (module `Product`), applied to
   `binaryGeometricPieceConstituents` (module `Pieces`). That theorem proves the auxiliary
   proposition `BinaryGeometricPieces.BinaryGeometricPieceConstituents` (module
   `Langlands.Representation.Classification.BinaryGeometricPieceConstituentsStatement`).
   The proposition describes the irreducible subquotients of the geometric-lemma pieces of
   the Jacquet module of a binary product. With the geometric lemma
   (`padicGeometricLemma`), Frobenius reciprocity and the fact that a supercuspidal
   representation is not a subquotient of a proper normalized product, it shows the
   following. If `Y₁` and `Y₂` have finite length and are left `A`-reduced, then so is
   `Y₁ × Y₂`.
3. **Comparison.** `comparison` (module `Clause3`). The main case uses the iterated product
   identification `A^K × Y ≅ (A × ⋯ × A) × Y` (module `PowerIso`) and the image argument of
   module `Comparison`.
4. **Uniqueness.** `uniqueness` (module `Clause4`). The main case uses the same
   identification and the multiplicity-one socle criterion for `(A × ⋯ × A) × S` (module
   `Uniqueness`, built on module `Core`).
5. **Segments.** `leftReduced_of_isSegmentHead` and `leftReduced_of_isSegmentSocle`
   (module `Segments`), from the ordered Jacquet modules of segment heads and socles.

## Helper modules

All helper modules are internal to this proof and documented in their own Markdown files:
`Basic`, `Frobenius`, `Segments`, `Criterion`, `FirstBlock`, `Product`, `PieceTools`,
`PieceTransport`, `PieceStructure`, `PieceCombinatorics`, `Pieces`, `Transitivity`,
`PowerSupport`, `Core`, `Uniqueness`, `PowerIso`, `Clause4`, `Comparison` and `Clause3`. The
auxiliary proposition lives in `BinaryGeometricPieceConstituentsStatement`.

## Sources

Jantzen 2007 (Definition 2.1.1, Lemma 2.1.2); Mínguez 2009 (§2 Lemma `mult1`, §3 Proposition
`JA`); Lapid–Mínguez 2016 (§1.2–1.3); Zelevinsky 1980 (Propositions 3.4 and 9.5);
Bernstein–Zelevinsky 1977 (geometric lemma). The Lean proof follows these arguments. It
uses the Library's geometric lemma, first adjointness, multiplicity-one socle criterion,
Jordan–Hölder multiplicities and supercuspidal support theory.
