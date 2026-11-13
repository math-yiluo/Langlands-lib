# All-field port of `Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesStatement`

`Langlands.AllField.Representation.RankinSelberg.FiniteFunctionShellSeriesStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Shell generating integrals of finite functions**

A derived internal proposition target for the valuation-shell route to the
one-variable Mellin argument of JPSS (1983), printed pages 391–392. The
coefficients are actual integrals over the integral units; one recurrence
and one convergence bound serve every Schwartz--Bruhat test function.
No analytic assertion is proved here.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.RankinSelberg.FiniteFunctionShellSeriesStatement` (def): Actual shell coefficients have a lower support bound and a uniformly
  recurrent tail. On one punctured disc, uniform over the full Schwartz--Bruhat
  space, their bilateral generating sum equals the actual integrable Haar
  integral weighted by the integer power of the normalized order.
