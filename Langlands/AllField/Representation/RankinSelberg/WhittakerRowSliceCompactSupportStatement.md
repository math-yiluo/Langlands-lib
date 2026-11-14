# All-field port of `Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement`

`Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact support of Whittaker row data on a determinant slice**

The compact-support assertion of JPSS (1983), Section 4.6, printed page 412,
for the norm of `W(g) Φ(η g)` on each fixed determinant slice of the actual
quotient `N_(n+1) \ GL_(n+1)`, for actual coefficient images of smooth
representations. This is a proposition definition; no proof is supplied.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.WhittakerRowSliceCompactSupportStatement` (def): On every determinant slice, the norm of `W(g) Φ(lastRow g)`, extended by zero
  off the slice, has compact support on the actual quotient topology. The scope is
  every actual coefficient image of every smooth representation, including zero
  functionals, zero coefficients, zero test functions and actual rank one.
