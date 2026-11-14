# All-field port of `Langlands.Representation.RankinSelberg.EqualRankSliceExpansionStatement`

`Langlands.AllField.Representation.RankinSelberg.EqualRankSliceExpansionStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankSliceExpansionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankSliceExpansionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Conditional equal-rank determinant-series expansion**

JPSS (1983), Section 4.2, (4.2.2), printed page 407: at any supplied
convergent parameter, the actual equal-rank integral is the absolutely
summable unordered sum of its determinant-slice coefficients with weight
`(q^(-s))^m`. All coefficients at zero are integrable on their slices.
This module states the conditional partition argument; it does not prove it.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankSliceExpansionStatement` (def): Conditional partition content of JPSS (4.2.2), for any measure on the
  Borel structure of the actual quotient: global convergence at `s` gives
  slice integrability at zero, absolute summability of the weighted scalar
  coefficients, and their `HasSum` to the actual integral at `s`.
