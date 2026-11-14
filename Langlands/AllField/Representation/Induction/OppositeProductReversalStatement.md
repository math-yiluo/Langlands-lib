# All-field port of `Langlands.Representation.Induction.OppositeProductReversalStatement`

`Langlands.AllField.Representation.Induction.OppositeProductReversalStatement` is the all-field port of the Library module `Langlands.Representation.Induction.OppositeProductReversalStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Induction.OppositeProductReversalStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Opposite induction and reversed upper block products**

An internal transport statement with both canonical evaluation formulas.
The block reversal preserves coordinates within each block.

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockFactors`
- `Langlands.AllField.Representation.Induction.OppositeParabolic`

## Declarations

- `Langlands.AllField.GLOppositeProductReversalStatement` (def): Opposite normalized induction of a block tensor is the upper normalized
  product of the reversed block family, with the specified function maps.
