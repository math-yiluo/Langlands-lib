# All-field port of `Langlands.Representation.Whittaker.MirabolicFunctionalTransfer`

`Langlands.AllField.Representation.Whittaker.MirabolicFunctionalTransfer` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicFunctionalTransfer`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicFunctionalTransfer` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Functional spaces and exactness inputs for the actual mirabolic restriction.

## Imports from the port

- `Langlands.AllField.Group.GL.UpperUnipotentCompactContainmentProof`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

## Declarations

- `Langlands.AllField.GeneralLinear.Mirabolic.upperUnipotent_isLimitOfCompactSubgroups` (theorem): Compact containment transports through the actual unipotent group
  identification, for the supplied field topology.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.character_isLocallyConstant_of_hasFunctional`, `Langlands.Whittaker.mirabolicFunctionalsEquiv`, `Langlands.Whittaker.mirabolicFunctionalsEquiv_val`, `Langlands.Whittaker.mirabolic_existsUnique_hasFunctional_factor`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
