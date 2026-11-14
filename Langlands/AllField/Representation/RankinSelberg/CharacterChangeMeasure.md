# All-field port of `Langlands.Representation.RankinSelberg.CharacterChangeMeasure`

`Langlands.AllField.Representation.RankinSelberg.CharacterChangeMeasure` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.CharacterChangeMeasure`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.CharacterChangeMeasure` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The character-change quotient Haar law from the subgroup modulus**

If conjugation by `d_a` pushes unipotent Haar measure forward to `c⁻¹` times
itself, then left translation by `d_a` pushes every compatible quotient measure
forward to `c` times itself. The proof shows that `c⁻¹` times the pushforward
is again compatible and applies quotient-measure uniqueness. The reduction is
then specialized to the canonical p-adic statement, and the published subgroup
law `unipotentCharacterChangeModulus` discharges its hypothesis.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.CharacterChangeMeasureStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnipotentCharacterChangeModulusProof`

## Declarations

- `Langlands.AllField.RankinSelberg.characterChangeCompatibleMeasure_of_unipotentModulus` (theorem): The subgroup modulus statement implies the canonical quotient law.
- `Langlands.AllField.RankinSelberg.characterChangeCompatibleMeasure` (theorem): Left translation by `d_a` multiplies every compatible quotient measure by the
  canonical character-change modulus.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.characterChangeConjHomeomorph`, `Langlands.RankinSelberg.rightTranslate_comp_characterChangeQuotient`, `Langlands.RankinSelberg.quotientAverage_characterChangeQuotient`, `Langlands.RankinSelberg.isCompatible_smul_map_characterChangeQuotient`, `Langlands.RankinSelberg.hasCharacterChangeMeasureLaw_of_unipotentModulus`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
