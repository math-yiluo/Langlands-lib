# All-field port of `Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement`

`Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Mellin integrals of finite functions on a torus over a nonarchimedean local field**

A proposition target derived from the tensor reduction and one-variable Mellin
argument in JPSS (1983), printed page 392, displays (5)-(6). The denominator is
uniform over all Schwartz--Bruhat test functions for a fixed finite family of
translation-finite functions. No analytic conclusion is assumed or proved here.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.RankinSelberg.FiniteFunctionMellinStatement` (def): Convergence, rational continuation in `q^(-s)`, and a common Laurent
  polynomial denominator for a finite family of finite functions on `(Fˣ)^r`.
  The positive integral weights include the JPSS weights `m i = i.val + 1`.
  All auxiliary functions and sets below are local to this proposition.
