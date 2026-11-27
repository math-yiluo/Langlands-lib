# All-field port of `Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationProof`

Lean module: `Langlands.AllFieldBZ.Representation.Unitary.LeviCuspidalRealUnitarizationProof`. Original module: `Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationProof`; its mathematical content is
described in the Library file `Langlands/Representation/Unitary/LeviCuspidalRealUnitarizationProof.md`.

## Content

`leviCuspidalRealUnitarization` proves `LeviCuspidalRealUnitarizationStatement`. The real twist removes the norm of the central character on the block scalars; Harish-Chandra's compactness on the determinant-unit subgroup and its finite index modulo the center make the twisted coefficient norms compactly supported on the central quotient, and integrating coefficient products against a Haar measure gives the invariant positive form.

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.LeviCuspidalRealUnitarization.blockScalarLevi_mem_center` | `Langlands.AllFieldBZ.LeviCuspidalRealUnitarization.blockScalarLevi_mem_center` |
| `Langlands.LeviCuspidalRealUnitarization.exists_blockScalarLevi_eq_of_mem_center` | `Langlands.AllFieldBZ.LeviCuspidalRealUnitarization.exists_blockScalarLevi_eq_of_mem_center` |
| `Langlands.LeviCuspidalRealUnitarization.coe_blockScalarCenter` | `Langlands.AllFieldBZ.LeviCuspidalRealUnitarization.coe_blockScalarCenter` |
| `Langlands.LeviCuspidalRealUnitarization.continuous_blockScalarCenter` | `Langlands.AllFieldBZ.LeviCuspidalRealUnitarization.continuous_blockScalarCenter` |
| `Langlands.LeviCuspidalRealUnitarization.leviRealPowerTwist_comp_determinantUnitInclusion` | `Langlands.AllFieldBZ.LeviCuspidalRealUnitarization.leviRealPowerTwist_comp_determinantUnitInclusion` |
| `Langlands.LeviCuspidalRealUnitarization.exists_leviRealPowerTwist_unitaryCentralCharacter` | `Langlands.AllFieldBZ.LeviCuspidalRealUnitarization.exists_leviRealPowerTwist_unitaryCentralCharacter` |
| `Langlands.leviCuspidalRealUnitarization` | `Langlands.AllFieldBZ.leviCuspidalRealUnitarization` |

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

The field-independent theorem `Langlands.UnitaryCentralCharacter.hasCompactSupport_coefficientNorm_of_finiteIndex` is used unchanged. The norm exponent of a smooth character of `F^×` comes from `Langlands.LocalFieldData.smoothCharacterNormDecomposition`, the block-scalar homomorphism into the center from `Langlands.AllField.Parabolic.blockScalarCenter`, and the finite index of the determinant-unit subgroup joined with the center from `Langlands.AllFieldBZ.CuspidalSupport.determinantUnit_sup_center_finiteIndex` (the original takes it from the p-adic structure theorem `leviDeterminantUnitStructure`).

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
