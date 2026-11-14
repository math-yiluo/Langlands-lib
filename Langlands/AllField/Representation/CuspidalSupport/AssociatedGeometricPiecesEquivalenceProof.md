# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof`

`Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Full-refinement identities and the conjugating geometric piece.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`

## Declarations

- `Langlands.AllField.CuspidalSupport.refinedModulus_eq_one_of_full` (theorem).
- `Langlands.AllField.CuspidalSupport.refinedHalfModulus_eq_one_of_full` (theorem).
- `Langlands.AllField.CuspidalSupport.refinedInverseHalfModulus_eq_one_of_full` (theorem).
- `Langlands.AllField.CuspidalSupport.fullRefinedJacquetEquiv` (def).
- `Langlands.AllField.CuspidalSupport.fullRefinedInductionEquiv` (def): Full normalized refined induction is evaluated at one, with its
  normalizing factor and projection reduced by proved full-refinement identities.
- `Langlands.AllField.CuspidalSupport.associatedGeometricPieceEquivalence` (theorem): A conjugating geometric piece is the actual whole-Levi transport.
  The extra quasicuspidality, association and minimality hypotheses of the
  published component are retained, although this identity does not need them.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.sourceLevi_eq_top_of_conjugates`, `Langlands.CuspidalSupport.targetLevi_eq_top_of_conjugates`, `Langlands.CuspidalSupport.refinedParabolic_eq_top_of_refinedLevi_eq_top`, `Langlands.CuspidalSupport.refinedLeviProjection_val_of_full`, `Langlands.CuspidalSupport.refinedUnipotent_eq_bot_of_full`, `Langlands.CuspidalSupport.innerParabolic_eq_top_of_full`, `Langlands.CuspidalSupport.fullInductionInverse`, `Langlands.CuspidalSupport.fullInductionEquiv`, `Langlands.CuspidalSupport.subgroupEqualityEquiv`, `Langlands.CuspidalSupport.intersectionLeviConjugation_symm_val`, `Langlands.CuspidalSupport.intersectionTransportFullEquiv`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
