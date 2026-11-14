# All-field port of `Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusStatement`

`Langlands.AllField.Representation.RankinSelberg.UnipotentCharacterChangeModulusStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unipotent Haar measure under character-change conjugation**

Conjugation by `d_a = diag(a^n, ..., a, 1)` scales the coordinate `(i,j)` of the
upper-unipotent group by `a^(j-i)`. The proposition below states that the actual
integral-normalized unipotent Haar measure is pushed forward to the reciprocal
modulus times itself. It does not prove that law. The two helper theorems only
show that the pushforward is along a continuous, hence Borel measurable, map.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnipotentCharacterChangeModulusStatement` (def): For every p-adic field with its supplied topological data, every rank `n + 1`
  and every unit `a`, conjugation `u ↦ d_a u d_a⁻¹` pushes the integral-normalized
  unipotent Haar measure forward to `|a|^(-E)` times itself, where
  `E = characterChangeRootExponent n` and `|·|` is the normalized absolute value.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.continuous_characterChangeConj`, `Langlands.RankinSelberg.measurable_characterChangeConj`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
