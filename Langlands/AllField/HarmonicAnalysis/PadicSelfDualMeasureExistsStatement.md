# All-field port of `Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement`

`Langlands.AllField.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

A focused scalar self-dual Haar existence target for each supplied local-field topology.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement` (def): Every continuous nontrivial unitary additive character admits a genuine
  self-dual additive Haar measure for the supplied local-field topology.
  Total disconnectedness is asserted explicitly as part of the conclusion.
