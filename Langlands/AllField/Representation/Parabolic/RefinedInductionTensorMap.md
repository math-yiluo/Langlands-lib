# All-field port of `Langlands.Representation.Parabolic.RefinedInductionTensorMap`

`Langlands.AllField.Representation.Parabolic.RefinedInductionTensorMap` is the all-field port of the Library module `Langlands.Representation.Parabolic.RefinedInductionTensorMap`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.RefinedInductionTensorMap` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The actual pointwise tensor map for normalized refined induction.

## Imports from the port

- `Langlands.AllField.Representation.Induction.Equivalences`
- `Langlands.AllField.Representation.Parabolic.RefinedInductionTensorNormalization`

## Declarations

- `Langlands.AllField.Parabolic.RefinedInductionTensor.productInducing_eq` (theorem): The literal product-subgroup inducing action is the actual normalized
  refined inducing action.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv` (def): Normalization identifies the inducing actions by the identity on their
  original tensor coefficient space.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.inducingNormalizationEquiv_apply` (theorem).
- `Langlands.AllField.Parabolic.RefinedInductionTensor.inducedNormalizationEquiv` (def): Identity postcomposition transports actual smooth induced functions from
  product covariance to the normalized refined covariance.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.pointwiseMap` (def): The pointwise tensor map with the actual normalized refined target.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.pointwiseMap_tprod_eval` (theorem): The map has precisely the evaluation prescribed for the eventual inverse
  in the published comparison statement.
