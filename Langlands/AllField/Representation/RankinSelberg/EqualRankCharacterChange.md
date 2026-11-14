# All-field port of `Langlands.Representation.RankinSelberg.EqualRankCharacterChange`

`Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankCharacterChange`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankCharacterChange` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rational equal-rank zeta transport under change of additive character**

The actual integral multiplier is a Laurent unit when the determinant absolute
value is an integer power of q. The quotient measure law remains explicit.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.normalizedDeterminantWeight_eq_spectralPoint_zpow` (theorem): The shared p-adic normalization supplies the determinant-order exponent.
- `Langlands.AllField.RankinSelberg.zetaSpan_equalRank_characterChange_normalized` (theorem): P-adic equal-rank span invariance needs only the explicit measure transport
  law; its numerical determinant normalization is discharged internally.
- `Langlands.AllField.RankinSelberg.isEqualRankLPolynomial_characterChange_normalized` (theorem): Under the same measure law, the p-adic normalized L-polynomial relation is
  unchanged by scaling the additive character. No generator existence is assumed.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.characterChangeScalar`, `Langlands.RankinSelberg.characterChangeLaurentUnit`, `Langlands.RankinSelberg.determinantWeight_eq_spectralPoint_zpow`, `Langlands.RankinSelberg.equalRankIntegral_characterChange_monomial`, `Langlands.RankinSelberg.equalRankIntegral_characterChange_monomial_reverse`, `Langlands.RankinSelberg.equalRankContinuation_characterChange`, `Langlands.RankinSelberg.equalRankContinuation_characterChange_reverse`, `Langlands.RankinSelberg.equalRankZetaValues_characterChange`, `Langlands.RankinSelberg.equalRankZetaValues_characterChange_reverse`, `Langlands.RankinSelberg.zetaSpan_equalRank_characterChange`, `Langlands.RankinSelberg.isEqualRankLPolynomial_characterChange`, `Langlands.RankinSelberg.normalizedGeneratorExists_equalRank_characterChange`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
