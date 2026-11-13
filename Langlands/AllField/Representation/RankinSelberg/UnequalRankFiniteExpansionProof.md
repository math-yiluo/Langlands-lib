# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankFiniteExpansionProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankFiniteExpansionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankFiniteExpansionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.exists_compactOpen_rectangular_subgroup` (theorem): Intersecting a pulled-back open subgroup with integral matrices makes it compact.
- `Langlands.AllField.RankinSelberg.unequalRank_coefficient_invariant` (theorem): Smoothness supplies one compact open translation subgroup for all block arguments.
- `Langlands.AllField.RankinSelberg.unequalRankFiniteExpansion_of_cosetExpansion` (theorem): The representation-specific assembly, conditional on the generic coset expansion.
- `Langlands.AllField.RankinSelberg.unequalRankFiniteExpansion` (theorem): Uniform compact support gives a finite pointwise Schwartz expansion in the
  original coefficient model, for all rectangular dimensions.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rectangularEntries_mul`, `Langlands.RankinSelberg.rectangularEntries_add`, `Langlands.RankinSelberg.rectangularUnipotent_zero`, `Langlands.RankinSelberg.rectangularUnipotent_add`, `Langlands.RankinSelberg.rectangularUnipotent_neg`, `Langlands.RankinSelberg.continuous_rectangularEntries`, `Langlands.RankinSelberg.continuous_rectangularUnipotent`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
