# All-field port of `Langlands.Representation.Parabolic.RefinedInductionTensorNormalization`

`Langlands.AllField.Representation.Parabolic.RefinedInductionTensorNormalization` is the all-field port of the Library module `Langlands.Representation.Parabolic.RefinedInductionTensorNormalization`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.RefinedInductionTensorNormalization` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Coordinate normalization for refined external tensor induction.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.RefinedInductionTensorStatement`

## Declarations

- `Langlands.LocalFieldData.refinedLeviBlock_projection` (theorem): The actual refined Levi projection has the expected inner block coordinates.
- `Langlands.LocalFieldData.refinedLeviHalfModulus_eq_prod` (theorem): The canonical positive half of the refined modulus is the product of the
  canonical positive halves on the actual inner Levi coordinates.
- `Langlands.LocalFieldData.refinedParabolicHalfModulus_eq_prod` (theorem): The refined parabolic normalizing character is the coordinatewise product.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.blockInducingRepresentation` (abbrev): The individual normalized inducing actions, before smooth induction.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.coordinateInducingRepresentation` (def): The tensor of the normalized block inducing actions in actual subgroup coordinates.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.normalizedRefinedInducingRepresentation` (abbrev): The actual normalized refined inducing action from the published statement.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.coordinateInducingRepresentation_eq` (theorem): Positive-half normalization commutes with this finite external tensor.
