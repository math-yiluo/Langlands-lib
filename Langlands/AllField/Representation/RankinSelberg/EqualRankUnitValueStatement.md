# All-field port of `Langlands.Representation.RankinSelberg.EqualRankUnitValueStatement`

`Langlands.AllField.Representation.RankinSelberg.EqualRankUnitValueStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankUnitValueStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankUnitValueStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**An actual equal-rank JPSS integral with rational value one**

This proposition isolates the unit test of JPSS (1983), printed page 393,
with the full telescope of `EqualRankAnalyticStatement`. It asserts no proof
of the test-vector construction, Kirillov surjectivity, or general rationality.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankUnitValueStatement` (def): Some actual coefficient vectors and Schwartz--Bruhat test function have
  rational continuation equal to one. This includes rank one and possibly
  reducible Whittaker-type representations, with every compatible quotient measure.
  It is a proposition definition, not a proof or an added hypothesis of analyticity.
