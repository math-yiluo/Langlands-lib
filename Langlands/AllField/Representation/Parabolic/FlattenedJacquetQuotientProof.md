# All-field port of `Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof`

`Langlands.AllField.Representation.Parabolic.FlattenedJacquetQuotientProof` is the all-field port of the Library module `Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Equivariant surjectivity of the flattened normalized Jacquet quotient**

Canonical positive halves of the published full modulus comparison identify
the two normalized actions on quotient representatives.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.FlattenedJacquetQuotientStatement`
- `Langlands.AllField.Representation.Parabolic.FlattenedRefinementModulusCalculation`

## Declarations

- `Langlands.LocalFieldData.flattenedLeviHalfModulus` (theorem).
- `Langlands.LocalFieldData.flattenedLeviInverseHalfModulus` (theorem).
- `Langlands.AllField.Parabolic.flattenJacquetMap_mk` (theorem).
- `Langlands.AllField.Parabolic.normalizedIteratedJacquet_mk` (theorem).
- `Langlands.AllField.Parabolic.flattenJacquetMap_action_mk` (theorem).
- `Langlands.AllField.Parabolic.flattenJacquetMap_equivariant_mk` (theorem).
- `Langlands.AllField.Parabolic.flattenJacquetMap_equivariant` (theorem).
- `Langlands.AllField.Parabolic.flattenedJacquetQuotientMap` (def).
- `Langlands.AllField.Parabolic.flattenedJacquetQuotient` (theorem): The prescribed flattened quotient map is a surjective intertwiner for the
  standard flattened and transported iterated normalized Jacquet actions.
