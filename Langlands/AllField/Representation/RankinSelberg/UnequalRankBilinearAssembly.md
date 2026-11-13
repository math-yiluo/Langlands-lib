# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankBilinearAssembly`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearAssembly` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankBilinearAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankBilinearAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual coefficient-model pullback and conditional unequal-rank descent.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankAssembly.unequalRankBilinearUniqueness_of_source_length` (theorem): The exact uniqueness target follows from a uniform bound on the original
  carriers. The source length bound remains an explicit hypothesis.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankAssembly.coefficientModelBilinearPullback`, `Langlands.RankinSelberg.UnequalRankAssembly.coefficientModelBilinearPullback_injective`, `Langlands.RankinSelberg.UnequalRankAssembly.coefficientModelBilinearPullback_covariant`, `Langlands.RankinSelberg.UnequalRankAssembly.coefficientModel_uniqueness_of_source`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
