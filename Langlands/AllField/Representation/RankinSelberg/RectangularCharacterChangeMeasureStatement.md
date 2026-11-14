# All-field port of `Langlands.Representation.RankinSelberg.RectangularCharacterChangeMeasureStatement`

`Langlands.AllField.Representation.RankinSelberg.RectangularCharacterChangeMeasureStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RectangularCharacterChangeMeasureStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.RectangularCharacterChangeMeasureStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rectangular Haar measure under JPSS character change**

These propositions state the positive-power pushforward law for the existing
inverse row scaling. They cover arbitrary rectangular additive Haar measures
and the actual JPSS product measure. They do not prove either measure law.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.CharacterChangeRectangularHaarStatement` (def): Inverse row scaling pushes every Borel rectangular additive Haar measure
  forward by the existing positive character-change modulus.
- `Langlands.AllField.RankinSelberg.CharacterChangeRectangularProductStatement` (def): The same law for the actual JPSS product of any shared scalar additive Haar
  measure, with canonical scalar Borel and entrywise product measurable structures.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.CharacterChangeRectangularMeasureStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
