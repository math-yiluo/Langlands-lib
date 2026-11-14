# All-field port of `Langlands.Representation.RankinSelberg.CharacterChangeSingletonBlocks`

`Langlands.AllField.Representation.RankinSelberg.CharacterChangeSingletonBlocks` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.CharacterChangeSingletonBlocks`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.CharacterChangeSingletonBlocks` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The character-change diagonal as a singleton Levi element**

The diagonal `d_a = diag(a^n, ..., a, 1)` is the Levi element of the singleton
shape with entries `a^(n-i)`. Its conjugation of the upper unipotent group is the
Levi action on the singleton radical, and its block modulus is
`|a|^(sum_{i<j}(j-i))`.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.leviModulus_characterChangeLevi_eq_pow` (theorem): The singleton block modulus of `characterChangeLevi a n` is
  `|a|^(sum_{i<j}(j-i))`, as a unit of `ℝ≥0`.
- `Langlands.AllField.RankinSelberg.leviModulus_characterChangeLevi` (theorem): The singleton block modulus of `characterChangeLevi a n` is the
  character-change modulus for the normalized absolute value.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.characterChangeLevi`, `Langlands.RankinSelberg.leviEmbedding_characterChangeLevi`, `Langlands.RankinSelberg.upperUnipotentEquivRadical_characterChangeConj`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
