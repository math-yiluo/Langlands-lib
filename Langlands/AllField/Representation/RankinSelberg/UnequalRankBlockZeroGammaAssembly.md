# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaAssembly`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroGammaAssembly` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Conditional universal assembly of the block-zero gamma statement**

The input consists of the three remaining universal proof obligations.
The assembly derives the dual Whittaker hypotheses and specializes the
actual analytic inputs; it does not prove those three obligations.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankBlockZeroGammaAssemblyInput` (def): Exact universal inputs sufficient for the block-zero gamma assembly.
  This proposition packages open proof obligations and does not assert them.
- `Langlands.AllField.RankinSelberg.UnequalRankBlockZeroGammaAssemblyInput.gammaExistence` (theorem): Discharge the universal assembly once its three actual statement proofs
  are supplied. No additional dual-type, nonvanishing or comparison hypothesis
  is needed. The unconditional target remains open until these inputs are proved.
