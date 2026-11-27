# All-field port of `Langlands.Representation.Classification.LanglandsData`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.LanglandsData`. Original module: `Langlands.Representation.Classification.LanglandsData`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/LanglandsData.md`.

## Content

The determinant-power twist `ν^s A = A ⊗ |det|^s` of a smooth representation of `GL_r(F)` (`determinantPowerTwist`), the twisted block family `(ν^(u_1) σ_1, …, ν^(u_r) σ_r)` (`twistedBlocks`) and its normalized product `twistedProductInduced`, with the induced isomorphism of products of isomorphic blocks.

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.PadicField.TopologicalData.segmentFactor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.determinantPowerTwist` |
| `Langlands.PadicField.TopologicalData.twistedBlocks` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.twistedBlocks` |
| `Langlands.PadicField.TopologicalData.twistedProductInduced` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.twistedProductInduced` |
| `Langlands.PadicField.TopologicalData.twistedProductInduced_representation` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.twistedProductInduced_representation` |
| `Langlands.PadicField.TopologicalData.twistedProductInducedIso` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.twistedProductInducedIso` |

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

Only the section on twisted products is ported; the Langlands data structures of the original module have no all-field version here. The original module takes the twist from `Langlands.PadicField.TopologicalData.segmentFactor` (module `Langlands.Representation.Classification.Segments`); the all-field name `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.segmentFactor` already denotes the twisted members of a segment, so the twist is defined here under the name `determinantPowerTwist`, with the same body.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
