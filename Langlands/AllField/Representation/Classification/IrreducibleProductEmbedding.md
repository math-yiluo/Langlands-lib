# All-field port of `Langlands.Representation.Classification.IrreducibleProductEmbedding`

`Langlands.AllField.Representation.Classification.IrreducibleProductEmbedding` is the all-field port of the Library module `Langlands.Representation.Classification.IrreducibleProductEmbedding`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Classification.IrreducibleProductEmbedding` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Blockwise cuspidal embeddings and injectivity of normalized products.

## Imports from the port

- `Langlands.AllField.Representation.Classification.IrreducibleProductEmbeddingStatement`
- `Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof`
- `Langlands.AllField.Representation.CuspidalSupport.CuspidalEmbeddingProof`
- `Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorStatement`
- `Langlands.AllField.Representation.CuspidalSupport.CuspidalityComparisonProof`
- `Langlands.AllField.Representation.CuspidalSupport.LeviTensorFactorizationProof`
- `Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatementSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountProof`
- `Langlands.AllField.Representation.Induction.Equivalences`
- `Langlands.AllField.Representation.Parabolic.NormalizedInductionStatementSupplement`
- `Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement`

## Declarations

- `Langlands.AllField.Classification.irreducible_supercuspidalProduct_embedding` (theorem): An irreducible smooth GL representation in an arbitrary carrier universe
  embeds in an actual normalized product of small supercuspidal factors.
- `Langlands.AllField.Classification.normalizedProduct_embedding_of_factor_embeddings` (theorem): Tensor and then induce a family of actual blockwise injections.
- `Langlands.AllField.Classification.irreducibleProduct_embedding` (theorem): The original product embeds into the product of blockwise supercuspidal
  inductions. This supplies the injection before regrouping and transitivity.
- `Langlands.AllField.Classification.irreducibleProductEmbedding` (theorem): The complete named blockwise embedding proposition.

Public declarations of the original that are not re-declared here: `Langlands.FiniteTensor.externalMap_injective`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
