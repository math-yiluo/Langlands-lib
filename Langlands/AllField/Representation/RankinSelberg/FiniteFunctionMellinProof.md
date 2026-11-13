# All-field port of `Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof`

`Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinStatement`
- `Langlands.AllField.Representation.RankinSelberg.OneVariableMellinProof`

## Declarations

- `Langlands.AllField.RankinSelberg.MellinAssembly.localHaar_sigmaFinite` (theorem).
- `Langlands.AllField.RankinSelberg.MellinAssembly.field_totallyDisconnected` (theorem).
- `Langlands.AllField.RankinSelberg.MellinAssembly.finiteFunctionMellin_of_inputs` (theorem).
- `Langlands.AllField.RankinSelberg.finiteFunctionMellin` (theorem): Actual torus Mellin convergence, rational continuation, and a Laurent
  denominator uniform over the finite family and all Schwartz--Bruhat tests.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.MellinAssembly.uniform_right`, `Langlands.RankinSelberg.MellinAssembly.continuation_mul`, `Langlands.RankinSelberg.MellinAssembly.continuation_prod`, `Langlands.RankinSelberg.MellinAssembly.commonDenominator_iUnion`, `Langlands.RankinSelberg.MellinAssembly.commonDenominator_products`, `Langlands.RankinSelberg.MellinAssembly.commonDenominator_subset`, `Langlands.RankinSelberg.MellinAssembly.sum_prod_analytic`, `Langlands.RankinSelberg.MellinAssembly.tensor_expansion_identity`, `Langlands.RankinSelberg.MellinAssembly.mellin_of_expansions`, `Langlands.RankinSelberg.MellinAssembly.mellin_family_of_each`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
