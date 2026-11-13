# All-field port of `Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesProof`

`Langlands.AllField.Representation.RankinSelberg.FiniteFunctionShellSeriesProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the shell generating integrals of finite functions**

This module proves `Langlands.AllField.RankinSelberg.FiniteFunctionShellSeriesStatement`.
The uniformizer is the one supplied by the valuation-shell decomposition, and the
recurrence and growth base are those of the translation orbit of the finite
function along that uniformizer. For a test function, the valuation cutoffs give
the lower support bound and constancy past the upper cutoff; integrating the orbit
recurrence over the integral units then gives the recurrent tail. The shell norm
integrals vanish below the lower cutoff and are dominated by a geometric series
with ratio `B * ‖z‖` on nonnegative shells, so the shell integrability criterion
and the shell-sum identity apply.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof`
- `Langlands.AllField.Representation.RankinSelberg.FiniteFunctionShellSeriesStatement`
- `Langlands.AllField.Representation.RankinSelberg.ValuationShellIntegrationProof`

## Declarations

- `Langlands.AllField.RankinSelberg.finiteFunctionShellSeries` (theorem): Proof of `FiniteFunctionShellSeriesStatement`: one uniformizer, one recurrence
  and one geometric base serve every Schwartz--Bruhat test function.
