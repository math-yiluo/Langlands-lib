# All-field port of `Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapStatement`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.IrreducibleTwoFactorProductSwapStatement`. Original module: `Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapStatement`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/IrreducibleTwoFactorProductSwapStatement.md`.

## Content

The proposition `IrreducibleTwoFactorProductSwap`: for irreducible smooth representations `α, β` of `GL_k(F)` with `k > 0`, if the upper normalized product `α × β` is irreducible then it is isomorphic to `β × α`. This is the irreducible equal-rank case of Zelevinsky 1980, Theorem 1.9. Its all-field proof is `Langlands.AllFieldBZ.Classification.irreducibleTwoFactorProductSwap`.

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.IrreducibleTwoFactorProductSwap` | `Langlands.AllFieldBZ.Classification.IrreducibleTwoFactorProductSwap` |

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

None.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
