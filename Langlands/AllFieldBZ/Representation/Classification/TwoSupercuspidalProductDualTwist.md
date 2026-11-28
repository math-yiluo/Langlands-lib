# All-field port of `Langlands.Representation.Classification.TwoSupercuspidalProductDualTwist`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.TwoSupercuspidalProductDualTwist`. Original module: `Langlands.Representation.Classification.TwoSupercuspidalProductDualTwist`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/TwoSupercuspidalProductDualTwist.md`.

## Content

The smooth dual of a normalized block product of admissible blocks is the product of the block smooth duals (`productSmoothDual`); a smooth determinant character commutes with normalized block products (`productCharacterTwist`); hence `ν (δ_1 × ⋯ × δ_r)~ ≅ ν δ_1~ × ⋯ × ν δ_r~` (`productDualTwist`), and for two supercuspidal blocks `ν (ρ × ρ')~ ≅ ν ρ~ × ν ρ'~` (`twoBlockDualTwist`), with the supercuspidal representation `ν ρ~` given by `dualTwist`.

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.ProductDualTwist.productSmoothDual` | `Langlands.AllFieldBZ.Classification.ProductDualTwist.productSmoothDual` |
| `Langlands.Classification.ProductDualTwist.productCharacterTwist` | `Langlands.AllFieldBZ.Classification.ProductDualTwist.productCharacterTwist` |
| `Langlands.Classification.ProductDualTwist.absCharacter` | `Langlands.AllFieldBZ.Classification.ProductDualTwist.absCharacter` |
| `Langlands.Classification.ProductDualTwist.productDualTwist` | `Langlands.AllFieldBZ.Classification.ProductDualTwist.productDualTwist` |
| `Langlands.Classification.ProductDualTwist.dualTwist` | `Langlands.AllFieldBZ.Classification.ProductDualTwist.dualTwist` |
| `Langlands.Classification.ProductDualTwist.twoBlockDualTwist` | `Langlands.AllFieldBZ.Classification.ProductDualTwist.twoBlockDualTwist` |

## Systematic changes

- `Langlands.PadicField.{u} p` becomes `Langlands.AllFieldBZ.LocalFieldPackage.{u}`; the prime
  `p` and its `Fact p.Prime` instance are removed from binders and quantifiers, and the
  corresponding explicit arguments are dropped.
- Normalization API names on `T` (for example `Integers`, `ord`, `normalizedAbs`, `uniformizer`)
  resolve to `Langlands.LocalFieldData`.
- Every ported declaration `Langlands.X` is renamed `Langlands.AllFieldBZ.X` (with
  `PadicField.TopologicalData` replaced by `LocalFieldPackage.TopologicalData`). References to
  declarations that already have all-field versions in the Library use those versions (for
  example `Langlands.AllFieldBZ.Derivative.generalLinearDerivative` for
  `Langlands.Derivative.generalLinearDerivative`, and the `_allFieldBZ` versions of the
  `Langlands.GeneralLinear` declarations such as `compactOpen_cofinal`).
- References to field-independent declarations of the original module and of other p-adic
  modules are written with their full original names, so those declarations are used unchanged.
  Private field-independent helpers, which cannot be referenced from another module, are
  repeated as private declarations.

## Changes beyond the systematic replacements

`productCharacterTwist` uses `Langlands.GeneralLinear.determinant_blockParabolic` for the
determinant of a parabolic element. The private lemma `determinant_leviEmbedding` applies the
same identity to the image of a Levi element under the section of the Levi projection.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
