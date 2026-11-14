# All-field port of `Langlands.Representation.Parabolic.RefinedInductionTensorProof`

`Langlands.AllField.Representation.Parabolic.RefinedInductionTensorProof` is the all-field port of the Library module `Langlands.Representation.Parabolic.RefinedInductionTensorProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.RefinedInductionTensorProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Tensor compatibility for normalized refined induction, with its canonical inverse.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Representation.Parabolic.RefinedInductionTensorMap`

## Declarations

- `Langlands.AllField.Parabolic.RefinedInductionTensor.pointwiseMap_bijective` (theorem): The generic compact-quotient bijectivity result specializes to the actual
  normalized refined pointwise map.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.comparison_of_pointwiseMap_bijective` (theorem): Bijectivity of the actual pointwise map constructs the requested equivalence
  and its canonical inverse, with the orientation in the published statement.
- `Langlands.AllField.Parabolic.refinedInductionTensor` (theorem): Normalized refined induction commutes with the finite external tensor
  product, with the prescribed pointwise pure-tensor inverse.
