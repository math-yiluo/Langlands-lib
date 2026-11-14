# All-field supplement to `Langlands.AllField.Representation.Induction.SingleBlock`

`Langlands.AllField.Representation.Induction.SingleBlockSupplement` supplements the Library module `Langlands.AllField.Representation.Induction.SingleBlock`, the existing all-field port of `Langlands.Representation.Induction.SingleBlock`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.Induction.SingleBlock` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Induction.SingleBlock` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Evaluation equivalences for single-block normalized induction.

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockFactors`
- `Langlands.AllField.Representation.Induction.SingleBlock`

## Declarations

- `Langlands.LocalFieldData.singleBlock_parabolicHalfModulus` (theorem).
- `Langlands.LocalFieldData.singleBlockNormalizedInducedEquiv` (def): Evaluation at the identity identifies normalized induction from a single block
  with the original Levi action transported to the ambient general linear group.
- `Langlands.LocalFieldData.singleBlockNormalizedInducedEquiv_apply` (theorem).
- `Langlands.LocalFieldData.singleBlockNormalizedInducedEquiv_symm_eval` (theorem).
- `Langlands.LocalFieldData.singleBlockNormalizedProductEquiv` (def): A one-block normalized product is its unique factor, after the explicit rank transport.
- `Langlands.LocalFieldData.singleBlockNormalizedProductEquiv_apply` (theorem): Product evaluation is evaluation at one followed by the existing singleton tensor map.

Declarations of the original re-declared by `Langlands.AllField.Representation.Induction.SingleBlock` and therefore not here: `Langlands.PadicField.TopologicalData.singleBlock_leviModulus`, `Langlands.PadicField.TopologicalData.singleBlock_leviHalfModulus`.

Public declarations of the original that are not re-declared here: `Langlands.Induction.smoothInducedTopEquiv`, `Langlands.Induction.smoothInducedTopEquiv_apply`, `Langlands.Induction.smoothInducedTopEquiv_symm_eval`, `Langlands.GeneralLinear.BlockShape.singleBlockLeviEquiv_symm_coordinate`, `Langlands.GeneralLinear.BlockShape.singleBlockTensorEquiv`, `Langlands.PadicField.TopologicalData.singleBlock_parabolicModulus`, `Langlands.PadicField.TopologicalData.singleBlockNormalizedInducedEquiv_left_inv`, `Langlands.PadicField.TopologicalData.singleBlockNormalizedInducedEquiv_right_inv`, `Langlands.PadicField.TopologicalData.singleBlockNormalizedInducedEquiv_action`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
