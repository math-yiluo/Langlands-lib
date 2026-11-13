# All-field port of `Langlands.Representation.RankinSelberg.ModelAsymptoticStatement`

`Langlands.AllField.Representation.RankinSelberg.ModelAsymptoticStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.ModelAsymptoticStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.ModelAsymptoticStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Torus expansions in coefficient models**

This is a conditional interface: the Whittaker-type torus expansion
`WhittakerTypeAsymptoticStatement` gives the expansion in the actual coefficient
models of JPSS integrals, for the topology of the same supplied data `T`. It does not assert the analytic expansion without its prerequisite.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`
- `Langlands.AllField.Representation.Whittaker.AsymptoticStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.ModelAsymptoticTransferStatement` (def): The Whittaker-type full-torus statement implies the expansion needed by JPSS
  coefficient models, for every supplied `T : LocalFieldData F` and either character sign.
  The implication retains the full Whittaker-type, possibly reducible scope.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.CoefficientTorusExpansion`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
