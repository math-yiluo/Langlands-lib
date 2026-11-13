# All-field port of `Langlands.Group.GL.CompactOpen`

`Langlands.AllField.Group.GL.CompactOpen` is the all-field port of the Library module `Langlands.Group.GL.CompactOpen`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Group.GL.CompactOpen` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact open subgroups for actual local-field matrix groups**

## Imports from the port

- `Langlands.AllField.Group.GL.PadicBlocks`
- `Langlands.AllField.Group.GL.PadicUpperUnipotent`

## Declarations

- `Langlands.LocalFieldData.generalLinearNonarchimedean` (theorem): The actual GL topology from any supplied local-field realization is nonarchimedean.
- `Langlands.LocalFieldData.leviNonarchimedean` (theorem): The actual product Levi is nonarchimedean in the supplied topology.
- `Langlands.LocalFieldData.upperUnipotentNonarchimedean` (theorem): The full upper unipotent subgroup is nonarchimedean in the supplied topology.
- `Langlands.LocalFieldData.upperUnipotentCompactOpen` (def): Choose a compact open subgroup inside an upper-unipotent identity neighborhood.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.parabolicNonarchimedean`, `Langlands.PadicField.TopologicalData.oppositeParabolicNonarchimedean`, `Langlands.PadicField.TopologicalData.unipotentRadicalNonarchimedean`, `Langlands.PadicField.TopologicalData.oppositeUnipotentRadicalNonarchimedean`, `Langlands.PadicField.TopologicalData.generalLinearCompactOpen`, `Langlands.PadicField.TopologicalData.parabolicCompactOpen`, `Langlands.PadicField.TopologicalData.oppositeParabolicCompactOpen`, `Langlands.PadicField.TopologicalData.unipotentRadicalCompactOpen`, `Langlands.PadicField.TopologicalData.oppositeUnipotentRadicalCompactOpen`, `Langlands.PadicField.TopologicalData.leviCompactOpen`, `Langlands.PadicField.canonicalGeneralLinearNonarchimedean`, `Langlands.PadicField.canonicalGeneralLinearCompactOpen`, `Langlands.PadicField.canonicalParabolicNonarchimedean`, `Langlands.PadicField.canonicalParabolicCompactOpen`, `Langlands.PadicField.canonicalOppositeParabolicNonarchimedean`, `Langlands.PadicField.canonicalOppositeParabolicCompactOpen`, `Langlands.PadicField.canonicalUnipotentRadicalNonarchimedean`, `Langlands.PadicField.canonicalUnipotentRadicalCompactOpen`, `Langlands.PadicField.canonicalOppositeUnipotentRadicalNonarchimedean`, `Langlands.PadicField.canonicalOppositeUnipotentRadicalCompactOpen`, `Langlands.PadicField.canonicalLeviNonarchimedean`, `Langlands.PadicField.canonicalLeviCompactOpen`, `Langlands.PadicField.canonicalUpperUnipotentNonarchimedean`, `Langlands.PadicField.canonicalUpperUnipotentCompactOpen`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation (see also the next paragraph).

The original abbreviation `canonicalUpperUnipotentCompactOpen` specializes `upperUnipotentCompactOpen` to `F.canonicalTopologicalData`. The port has no canonical data, and its users take `Langlands.LocalFieldData.upperUnipotentCompactOpen` for the supplied `T` instead, so the abbreviation is not ported.
