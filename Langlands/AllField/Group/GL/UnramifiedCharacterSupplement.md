# All-field supplement to `Langlands.AllField.Group.GL.UnramifiedCharacter`

`Langlands.AllField.Group.GL.UnramifiedCharacterSupplement` supplements the Library module `Langlands.AllField.Group.GL.UnramifiedCharacter`, the existing all-field port of `Langlands.Group.GL.UnramifiedCharacter`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Group.GL.UnramifiedCharacter` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Group.GL.UnramifiedCharacter` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**All complex unramified determinant characters**

The character with uniformizer value `z : ℂˣ` is `x ↦ z ^ ord(x)`.
This uses the actual normalized valuation and matrix determinant. Its kernel
is open, so the resulting character is continuous for the usual topology on `ℂ`.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.Group.GL.UnramifiedCharacter`

## Declarations

- `Langlands.LocalFieldData.unramifiedCharacter` (def): All complex values are allowed; there is no real-power or unitary restriction.
- `Langlands.LocalFieldData.unramifiedCharacter_apply` (theorem).
- `Langlands.LocalFieldData.ker_ordUnits_le_ker_unramifiedCharacter` (theorem).
- `Langlands.LocalFieldData.isOpen_ker_unramifiedCharacter` (theorem).
- `Langlands.LocalFieldData.continuous_unramifiedCharacter` (theorem).
- `Langlands.LocalFieldData.unramifiedCharacterContinuous` (def): The same character with its proved continuity bundled.
- `Langlands.LocalFieldData.determinantUnramifiedCharacter` (def): The actual determinant pullback of the unramified field character.
- `Langlands.LocalFieldData.determinantUnramifiedCharacter_apply` (theorem).
- `Langlands.LocalFieldData.isOpen_ker_determinantUnramifiedCharacter` (theorem).

Declarations of the original re-declared by `Langlands.AllField.Group.GL.UnramifiedCharacter` and therefore not here: `Langlands.PadicField.TopologicalData.ordUnits`, `Langlands.PadicField.TopologicalData.ordUnits_apply`, `Langlands.PadicField.TopologicalData.ord_eq_zero_iff_normalizedAbs`, `Langlands.PadicField.TopologicalData.ker_ordUnits`, `Langlands.PadicField.TopologicalData.uniformizerUnit`, `Langlands.PadicField.TopologicalData.uniformizerUnit_val`.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.unramifiedCharacterHom`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_one`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_mul`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_inv`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_uniformizer`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_injective`, `Langlands.PadicField.TopologicalData.IsUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.isUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.eq_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.unramifiedCharacterEquiv`, `Langlands.PadicField.TopologicalData.continuous_of_isUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_one`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_mul`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_inv`, `Langlands.PadicField.TopologicalData.ker_determinant_le_ker_determinantUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.ker_determinantNorm_le_ker_determinantUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_scalar`, `Langlands.PadicField.TopologicalData.realPowerCharacter_eq_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.realPowerDeterminant_eq_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacterContinuous`, `Langlands.PadicField.TopologicalData.norm_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.norm_determinantUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.norm_unramifiedCharacter_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
