# All-field port of `Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport`

`Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Measure support for lower-block quotient disintegration**

Right Haar measure on the actual lower triangular group, positive finite
compact open volumes, and integral transfer from a positive scaled pushforward.
These results do not assert the lower-block measure identity.

## Imports from the port

- `Langlands.AllField.Group.GL.PadicBlocksSupplement`
- `Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.lowerTriangularRightHaar` (def): Inversion sends a left Haar measure to a right Haar measure on the actual
  lower triangular group, with no normalization imposed.
- `Langlands.AllField.RankinSelberg.lowerTriangularRightHaar_properties` (theorem): All regularity, finiteness and right-invariance properties required of the
  triangular measure in lower-block disintegration.
- `Langlands.AllField.RankinSelberg.rectangularMeasure_compactOpen_pos_lt_top` (theorem): Every compact open additive parameter subgroup has positive finite volume
  for every supplied scalar Haar measure.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.lowerTriangularSubgroup_isClosed`, `Langlands.RankinSelberg.complex_integral_transfer_of_positive_scaled_map`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
