# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Continued unequal-rank bilinear forms at block zero**

This conditional interface isolates the construction of the actual continued
integrals with the covariance of JPSS (2.11.2) and (2.11.4). It states neither
analytic continuation existence nor bilinear uniqueness nor gamma existence.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement` (def): Conditional construction of the two block-zero continued bilinear forms.
  The only analytic premises are the original `(0,k)` and inverse-transpose
  `(k,0)` analytic inputs. The full Whittaker-type hypotheses and the supplied
  additive Haar measure are retained; no uniqueness or gamma theorem is assumed.
  This proposition definition does not prove the analytic inputs or covariance.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankBlockZeroContinuedFormsConclusion`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
