# All-field port of `Langlands.Group.GL.BlockModulusHaarProof`

`Langlands.AllField.Group.GL.BlockModulusHaarProof` is the all-field port of the Library module `Langlands.Group.GL.BlockModulusHaarProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Group.GL.BlockModulusHaarProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusHaarStatement`
- `Langlands.AllField.Group.GL.BlockUnipotentHaarProof`
- `Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof`

## Declarations

- `Langlands.LocalFieldData.leviModulus_eq_upperPair_prod` (theorem).
- `Langlands.AllField.glBlockModulusHaarStatement_of_prerequisites` (theorem).
- `Langlands.AllField.glBlockModulusHaarStatement_of_rectangular` (theorem): The coordinate-Haar result reduces the modulus formula to rectangular scaling.
- `Langlands.AllField.glBlockModulusHaar` (theorem): The explicit block modulus is the Haar module of Levi conjugation.
