# All-field port of `Langlands.Representation.Twist.LeviRealPower`

Lean module: `Langlands.AllFieldBZ.Representation.Twist.LeviRealPower`. Original module: `Langlands.Representation.Twist.LeviRealPower`; its mathematical content is
described in the Library file `Langlands/Representation/Twist/LeviRealPower.md`.

## Content

Real determinant characters `m ↦ ∏ᵢ |det mᵢ|^(tᵢ)` on standard product Levis (`leviRealPowerCharacter`) and the corresponding twists of Levi representations (`leviRealPowerTwist`), with their algebraic laws, open kernels and values on block scalars.

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.PadicField.TopologicalData.leviRealPowerCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerCharacter` |
| `Langlands.PadicField.TopologicalData.leviRealPowerCharacter_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerCharacter_apply` |
| `Langlands.PadicField.TopologicalData.coe_leviRealPowerCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.coe_leviRealPowerCharacter` |
| `Langlands.PadicField.TopologicalData.leviRealPowerCharacter_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerCharacter_zero` |
| `Langlands.PadicField.TopologicalData.leviRealPowerCharacter_add` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerCharacter_add` |
| `Langlands.PadicField.TopologicalData.leviRealPowerCharacter_neg` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerCharacter_neg` |
| `Langlands.PadicField.TopologicalData.normOneLevi_le_ker_leviRealPowerCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normOneLevi_le_ker_leviRealPowerCharacter` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_leviRealPowerCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_leviRealPowerCharacter` |
| `Langlands.PadicField.TopologicalData.coe_leviRealPowerCharacter_blockScalar` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.coe_leviRealPowerCharacter_blockScalar` |
| `Langlands.PadicField.TopologicalData.coe_leviRealPowerCharacter_scalar` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.coe_leviRealPowerCharacter_scalar` |
| `Langlands.PadicField.TopologicalData.leviRealPowerTwist` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerTwist` |
| `Langlands.PadicField.TopologicalData.leviRealPowerTwist_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerTwist_apply` |
| `Langlands.PadicField.TopologicalData.leviRealPowerTwist_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerTwist_zero` |
| `Langlands.PadicField.TopologicalData.leviRealPowerTwist_add` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerTwist_add` |
| `Langlands.PadicField.TopologicalData.leviRealPowerTwist_neg_cancel` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerTwist_neg_cancel` |
| `Langlands.PadicField.TopologicalData.leviRealPowerTwist_cancel_neg` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviRealPowerTwist_cancel_neg` |
| `Langlands.PadicField.TopologicalData.isSmooth_leviRealPowerTwist_iff` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isSmooth_leviRealPowerTwist_iff` |

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

`leviRealPowerCharacter_eq_topologicalData` (equality of the characters for two topological data on the same field) is not ported. Its p-adic proof rests on the uniqueness of the local-field structure of a finite extension of `ℚ_p`; it is not used by the declarations ported here.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
