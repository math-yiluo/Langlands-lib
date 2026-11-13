# All-field port of `Langlands.Group.GL.UnramifiedCharacter`

`Langlands.AllField.Group.GL.UnramifiedCharacter` is the all-field port of the Library module `Langlands.Group.GL.UnramifiedCharacter`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Group.GL.UnramifiedCharacter` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**All complex unramified determinant characters**

The character with uniformizer value `z : ℂˣ` is `x ↦ z ^ ord(x)`.
This uses the actual normalized valuation and matrix determinant. Its kernel
is open, so the resulting character is continuous for the usual topology on `ℂ`.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacter`

## Declarations

- `Langlands.LocalFieldData.ordUnits` (def): The normalized additive order on nonzero field elements, in multiplicative notation.
- `Langlands.LocalFieldData.ordUnits_apply` (theorem).
- `Langlands.LocalFieldData.ord_eq_zero_iff_normalizedAbs` (theorem): On nonzero elements, order zero is exactly normalized absolute value one.
- `Langlands.LocalFieldData.ker_ordUnits` (theorem).
- `Langlands.LocalFieldData.uniformizerUnit` (abbrev): The chosen uniformizer as a field unit, reusing the shared constructor.
- `Langlands.LocalFieldData.uniformizerUnit_val` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.unramifiedCharacter`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_apply`, `Langlands.PadicField.TopologicalData.unramifiedCharacterHom`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_one`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_mul`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_inv`, `Langlands.PadicField.TopologicalData.ker_ordUnits_le_ker_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.isOpen_ker_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.continuous_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.unramifiedCharacterContinuous`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_uniformizer`, `Langlands.PadicField.TopologicalData.unramifiedCharacter_injective`, `Langlands.PadicField.TopologicalData.IsUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.isUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.eq_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.unramifiedCharacterEquiv`, `Langlands.PadicField.TopologicalData.continuous_of_isUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_apply`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_one`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_mul`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_inv`, `Langlands.PadicField.TopologicalData.isOpen_ker_determinantUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.ker_determinant_le_ker_determinantUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.ker_determinantNorm_le_ker_determinantUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacter_scalar`, `Langlands.PadicField.TopologicalData.realPowerCharacter_eq_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.realPowerDeterminant_eq_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.determinantUnramifiedCharacterContinuous`, `Langlands.PadicField.TopologicalData.norm_unramifiedCharacter`, `Langlands.PadicField.TopologicalData.norm_determinantUnramifiedCharacter`, `Langlands.PadicField.TopologicalData.norm_unramifiedCharacter_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
