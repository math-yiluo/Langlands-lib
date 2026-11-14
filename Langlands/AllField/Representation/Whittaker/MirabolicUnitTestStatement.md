# All-field port of `Langlands.Representation.Whittaker.MirabolicUnitTestStatement`

`Langlands.AllField.Representation.Whittaker.MirabolicUnitTestStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicUnitTestStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicUnitTestStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact opposite-character mirabolic test functions**

An existence target for the compact mirabolic functions used before the
Kirillov lift in the equal-rank JPSS argument. This module defines a proposition;
it supplies neither its proof nor an integral identity.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicUnitTestStatement` (def): Compact opposite-character functions on the actual mirabolic subgroup,
  extended by zero to the ambient general linear group.

  The common compact open right stabilizer has normalized determinant norm one.
  An ambient compact open subgroup restricts inside this stabilizer, providing
  the ambient formulation of smoothness on the mirabolic subgroup only.
