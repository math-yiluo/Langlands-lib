# All-field port of `Langlands.Representation.Parabolic.JacquetFiniteGenerationProof`

`Langlands.AllField.Representation.Parabolic.JacquetFiniteGenerationProof` is the all-field port of the Library module `Langlands.Representation.Parabolic.JacquetFiniteGenerationProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.JacquetFiniteGenerationProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Finite generation of the actual normalized standard Jacquet module.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`
- `Langlands.AllField.Representation.Parabolic.JacquetFiniteGenerationStatement`

## Declarations

- `Langlands.AllField.Parabolic.JacquetFiniteGeneration.finite_of_compactQuotient` (theorem): Compactness of the parabolic quotient turns finitely many smooth ambient
  generators into finitely many generators of the normalized Jacquet module.
- `Langlands.AllField.Parabolic.normalizedJacquetFiniteGeneration` (theorem): Smooth finite generation is preserved by every actual normalized standard
  GL Jacquet functor, including rank zero and arbitrary carrier universe.
