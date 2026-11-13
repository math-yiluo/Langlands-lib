# All-field port of `Langlands.Group.GL.PadicBlocks`

`Langlands.AllField.Group.GL.PadicBlocks` is the all-field port of the Library module `Langlands.Group.GL.PadicBlocks`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Group.GL.PadicBlocks` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.LocalFieldData.unipotentRadicalTopology` (abbrev): The unipotent radical topology induced by the supplied field realization.
- `Langlands.LocalFieldData.unipotentRadicalTopologicalGroup` (theorem): The unipotent radical is a topological group for this exact topology.
- `Langlands.LocalFieldData.unipotentRadicalT2Space` (theorem): The unipotent radical is Hausdorff for this exact topology.
- `Langlands.LocalFieldData.unipotentRadicalLocallyCompactSpace` (theorem): The unipotent radical is locally compact for this exact topology.
- `Langlands.LocalFieldData.leviTopology` (abbrev): The Levi product topology induced by the supplied field realization.
- `Langlands.LocalFieldData.leviTopologicalGroup` (theorem): The Levi product is a topological group for this exact topology.
- `Langlands.LocalFieldData.leviT2Space` (theorem): The Levi product is Hausdorff for this exact topology.
- `Langlands.LocalFieldData.leviLocallyCompactSpace` (theorem): The Levi product is locally compact for this exact topology.
- `Langlands.LocalFieldData.blockLeviEmbedding` (def): The continuous Levi embedding for every supplied local-field realization.
- `Langlands.LocalFieldData.blockLeviProjection` (def): The continuous Levi projection for every supplied local-field realization.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.parabolicTopology`, `Langlands.PadicField.TopologicalData.parabolicTopologicalGroup`, `Langlands.PadicField.TopologicalData.parabolicT2Space`, `Langlands.PadicField.TopologicalData.parabolicLocallyCompactSpace`, `Langlands.PadicField.TopologicalData.oppositeParabolicTopology`, `Langlands.PadicField.TopologicalData.oppositeParabolicTopologicalGroup`, `Langlands.PadicField.TopologicalData.oppositeParabolicT2Space`, `Langlands.PadicField.TopologicalData.oppositeParabolicLocallyCompactSpace`, `Langlands.PadicField.TopologicalData.blockDecomposition`, `Langlands.PadicField.canonicalParabolicTopology`, `Langlands.PadicField.canonicalParabolicTopologicalGroup`, `Langlands.PadicField.canonicalParabolicT2Space`, `Langlands.PadicField.canonicalParabolicLocallyCompactSpace`, `Langlands.PadicField.canonicalOppositeParabolicTopology`, `Langlands.PadicField.canonicalOppositeParabolicTopologicalGroup`, `Langlands.PadicField.canonicalOppositeParabolicT2Space`, `Langlands.PadicField.canonicalOppositeParabolicLocallyCompactSpace`, `Langlands.PadicField.canonicalUnipotentRadicalTopology`, `Langlands.PadicField.canonicalUnipotentRadicalTopologicalGroup`, `Langlands.PadicField.canonicalUnipotentRadicalT2Space`, `Langlands.PadicField.canonicalUnipotentRadicalLocallyCompactSpace`, `Langlands.PadicField.canonicalLeviTopology`, `Langlands.PadicField.canonicalLeviTopologicalGroup`, `Langlands.PadicField.canonicalLeviT2Space`, `Langlands.PadicField.canonicalLeviLocallyCompactSpace`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
