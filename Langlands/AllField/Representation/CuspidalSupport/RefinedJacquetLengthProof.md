# All-field port of `Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof`

`Langlands.AllField.Representation.CuspidalSupport.RefinedJacquetLengthProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Finite length detected by the proper refined Jacquet modules of a product Levi.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.RefinedJacquetLengthStatement`
- `Langlands.AllField.Representation.Jacquet.Parabolic`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement`
- `Langlands.AllField.Representation.Parabolic.UnipotentFiniteContainment`

## Declarations

- `Langlands.AllField.CuspidalSupport.RefinedJacquetLengthProof.map_toLinearMap` (theorem): Normalization changes the action, but the actual quotient linear map is
  precisely the refined unipotent coinvariant map.
- `Langlands.AllField.CuspidalSupport.RefinedJacquetLengthProof.map_injective` (theorem): Refined Jacquet descent preserves an injection into a smooth representation.
- `Langlands.AllField.CuspidalSupport.RefinedJacquetLengthProof.map_exact` (theorem): Exactness on the actual refined quotient maps, with only the middle
  representation required to be smooth.
- `Langlands.AllField.CuspidalSupport.RefinedJacquetLengthProof.length_le` (theorem): Module length is monotone under the refined Jacquet map of a smooth injection.
- `Langlands.AllField.CuspidalSupport.RefinedJacquetLengthProof.length_step` (theorem): Additivity for the actual successive quotient of nested smooth invariant subspaces.
- `Langlands.AllField.CuspidalSupport.refinedJacquetFiniteLengthDetection` (theorem): The closed product-Levi criterion: absence of nonzero quasicuspidal
  subquotients and finite length of all proper refined Jacquet modules imply finite length.
