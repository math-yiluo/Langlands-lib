# All-field port of `Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly`

`Langlands.AllField.Representation.CuspidalSupport.LeviDecompositionAssembly` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual determinant-unit topology and conditional Levi decomposition.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulus`
- `Langlands.AllField.Group.GL.CompactOpen`
- `Langlands.AllField.Representation.CuspidalSupport.HarishChandraStatement`
- `Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalStructureStatement`

## Declarations

- `Langlands.AllField.CuspidalSupport.determinantUnitNonarchimedean` (theorem): The actual determinant-unit subgroup is nonarchimedean in its subtype topology.
- `Langlands.AllField.CuspidalSupport.determinantUnitLocallyCompactSpace` (theorem): Openness in the locally compact actual Levi supplies local compactness.
- `Langlands.AllField.CuspidalSupport.leviQuasicuspidalDecomposition_of_inputs` (theorem): The exact published Levi decomposition follows from the four analytic
  inputs and Harish-Chandra's criterion. No additional topology is assumed.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.leviCompactProjector`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
