# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankSourceAssembly`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankSourceAssembly` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankSourceAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankSourceAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Conditional source-length specialization of the separate-group assembly.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearAssembly`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankSourceLengthBoundStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankSpecializationInputs`
- `Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthStatement`
- `Langlands.AllField.Representation.Whittaker.MirabolicFunctionalMultiplicityProof`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankAssembly.pair_control_of_statements` (theorem): The exact rigidity and compact/generic statements supply the pair-control
  premise of the mixed finite-length assembly. Both statements remain premises.
- `Langlands.AllField.RankinSelberg.UnequalRankAssembly.sourceLengthBound_of_statements` (theorem): The three exact source statements imply the unchanged source length target.
  This compatibility theorem proves none of those three premises.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankAssembly.SourcePrerequisites`, `Langlands.RankinSelberg.UnequalRankAssembly.unequalRankBilinearUniqueness_of_statements`, `Langlands.RankinSelberg.UnequalRankAssembly.sourceLengthBound_of_prerequisites`, `Langlands.RankinSelberg.UnequalRankAssembly.unequalRankBilinearUniqueness_of_prerequisites`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
