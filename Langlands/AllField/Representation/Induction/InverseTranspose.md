# All-field port of `Langlands.Representation.Induction.InverseTranspose`

`Langlands.AllField.Representation.Induction.InverseTranspose` is the all-field port of the Library module `Langlands.Representation.Induction.InverseTranspose`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Induction.InverseTranspose` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Inverse-transpose transport of actual normalized block induction.

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockFactors`
- `Langlands.AllField.Representation.Induction.OppositeParabolic`

## Declarations

- `Langlands.LocalFieldData.determinantNorm_inverseTranspose` (theorem): Transposition preserves the determinant, so inverse transpose inverts its normalized norm.
- `Langlands.LocalFieldData.leviModulus_inverseTranspose` (theorem): Each determinant factor in the explicit upper modulus inverts, without changing block order.
- `Langlands.LocalFieldData.leviHalfModulus_inverseTranspose` (theorem): The canonical positive square root respects the derived full-modulus inversion.
- `Langlands.LocalFieldData.parabolicHalfModulus_oppositeToUpperInverseTranspose` (theorem): The positive upper half modulus under inverse transpose is the opposite half modulus.
- `Langlands.LocalFieldData.inverseTransposeProductInducing` (theorem): The actual normalized inducing actions agree on inverse-transposed lower elements.
- `Langlands.LocalFieldData.inverseTransposeProductToOppositeEquiv` (def): Precomposition by inverse transpose transports normalized upper block induction
  with pulled-back ambient action to normalized opposite induction of the pulled-back factors.
- `Langlands.LocalFieldData.inverseTransposeProductToOppositeEquiv_eval` (theorem).
- `Langlands.LocalFieldData.inverseTransposeProductToOppositeEquiv_symm_eval` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.Induction.precomposeSmoothFunction`, `Langlands.Induction.precomposeSmoothInducedEquiv`, `Langlands.Induction.precomposeSmoothInducedEquiv_eval`, `Langlands.Induction.precomposeSmoothInducedEquiv_symm_eval`, `Langlands.Induction.precomposeSmoothInducedEquiv_stabilizer`, `Langlands.Induction.precomposeSmoothInducedEquiv_symm_stabilizer`, `Langlands.GeneralLinear.BlockShape.oppositeToUpperInverseTranspose`, `Langlands.GeneralLinear.BlockShape.oppositeToUpperInverseTranspose_apply`, `Langlands.GeneralLinear.BlockShape.leviProjection_oppositeToUpperInverseTranspose`, `Langlands.GeneralLinear.BlockShape.blockTensor_inverseTranspose`, `Langlands.GeneralLinear.BlockShape.blockTensor_leviProjection_inverseTranspose`, `Langlands.PadicField.TopologicalData.inverseTransposeProductToOppositeEquiv_stabilizer`, `Langlands.PadicField.TopologicalData.inverseTransposeProductToOppositeEquiv_symm_stabilizer`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
