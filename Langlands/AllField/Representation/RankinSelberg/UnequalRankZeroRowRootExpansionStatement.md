# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankZeroRowRootExpansionStatement`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowRootExpansionStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankZeroRowRootExpansionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankZeroRowRootExpansionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform root expansions of zero-row unequal-rank coefficients**

This internal conditional statement isolates the pointwise root expansion
behind the diagonal restriction in JPSS, printed page 394, display (7).
The two full-torus expansion premises supply the finite-function families.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.ModelAsymptoticStatement`
- `Langlands.AllField.Representation.RankinSelberg.QuotientRootIntegrationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankZeroRowRootExpansionStatement` (def): A fixed finite family of continuous translation-finite functions expands
  all actual zero-row coefficient products at compact right translates.
  The determinant shift is included in that family, before the spectral parameter
  is chosen. No analytic convergence or extra representation hypothesis is used.
