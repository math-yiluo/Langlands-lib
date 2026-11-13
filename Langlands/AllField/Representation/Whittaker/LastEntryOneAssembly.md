# All-field port of `Langlands.Representation.Whittaker.LastEntryOneAssembly`

`Langlands.AllField.Representation.Whittaker.LastEntryOneAssembly` is the all-field port of the Library module `Langlands.Representation.Whittaker.LastEntryOneAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.LastEntryOneAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Coordinates and scalar assembly for the last-entry-one expansion**

Coordinate and scalar-functional bookkeeping used by the closed proof in
`LastEntryOneAsymptoticProof`. The assembly helper takes a root expansion as input.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RootCoordinateProof`
- `Langlands.AllField.Representation.Whittaker.LastEntryOneAsymptoticStatement`

## Declarations

- `Langlands.AllField.WhittakerLastEntryOne.rootHom_rootLift` (theorem): The existing full coordinate theorem recovers every root of this section.
- `Langlands.AllField.WhittakerLastEntryOne.rootLift_last` (theorem): The cumulative-product section has last entry one, also when `n = 0`.
- `Langlands.AllField.WhittakerLastEntryOne.rootLift_rootHom` (theorem): Every last-entry-one diagonal is recovered from its simple roots.
- `Langlands.AllField.WhittakerLastEntryOne.pullback_injective` (theorem): Pullback has no collisions because the root map has a section.
- `Langlands.AllField.WhittakerLastEntryOne.assemble` (theorem): A uniform root-coordinate expansion for one spanning functional gives
  the target's finite set on the full torus, uniformly for all functionals.

Public declarations of the original that are not re-declared here: `Langlands.WhittakerLastEntryOne.IsFiniteFunction`, `Langlands.WhittakerLastEntryOne.torus`, `Langlands.WhittakerLastEntryOne.rootHom`, `Langlands.WhittakerLastEntryOne.roots`, `Langlands.WhittakerLastEntryOne.rootLift`, `Langlands.WhittakerLastEntryOne.continuous_rootHom`, `Langlands.WhittakerLastEntryOne.finiteFunction_pullback`, `Langlands.WhittakerLastEntryOne.mem_glFunctionals_of_raw`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
