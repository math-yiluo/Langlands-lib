# All-field port of `Langlands.Representation.RankinSelberg.OneVariableMellinStatement`

`Langlands.AllField.Representation.RankinSelberg.OneVariableMellinStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.OneVariableMellinStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.OneVariableMellinStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Weighted one-variable Mellin integrals of finite functions**

A proposition target derived from JPSS (1983), printed page 392, display (6)
and the following paragraphs. The common denominator is uniform over the
entire Schwartz--Bruhat space for a fixed continuous translation-finite
function and positive integral weight. No analytic conclusion is proved here.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.RankinSelberg.OneVariableMellinStatement` (def): Actual convergence, rational continuation in `q^(-s)`, and one common
  Laurent denominator for the weighted Mellin integrals of a finite function.
  All auxiliary functions and sets are local to this proposition.
