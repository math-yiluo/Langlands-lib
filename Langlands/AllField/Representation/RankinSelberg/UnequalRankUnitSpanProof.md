# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankUnitSpanProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankUnitSpanProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankUnitSpanProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankUnitSpanProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unit membership in every actual unequal-rank JPSS zeta span**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof`
- `Langlands.AllField.Representation.Whittaker.ModelKirillovProof`
- `Langlands.AllField.Representation.Whittaker.WhittakerTypeKirillovProof`

## Declarations

- `Langlands.AllField.RankinSelberg.UnitSpanAssembly.unitSpan_of_kirillov_and_compact_test` (theorem): Assemble the compact test and its actual coefficient lift using the exact interfaces.
- `Langlands.AllField.RankinSelberg.UnitSpanAssembly.unitSpan_of_compact_test` (theorem): Use Whittaker-type Kirillov surjectivity (`whittakerTypeKirillov`) to lift a
  supplied compact test into the specified model.
- `Langlands.AllField.RankinSelberg.unequalRankUnitSpan` (theorem): Every actual unequal-rank JPSS zeta span contains one.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnitSpanAssembly.block_last_row`, `Langlands.RankinSelberg.UnitSpanAssembly.integrand_eq_of_mirabolic_eq`, `Langlands.RankinSelberg.UnitSpanAssembly.converges_iff_of_mirabolic_eq`, `Langlands.RankinSelberg.UnitSpanAssembly.integral_eq_of_mirabolic_eq`, `Langlands.RankinSelberg.UnitSpanAssembly.one_mem_of_unit_integral`, `Langlands.RankinSelberg.UnitSpanAssembly.one_mem_of_mirabolic_unit_integral`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
