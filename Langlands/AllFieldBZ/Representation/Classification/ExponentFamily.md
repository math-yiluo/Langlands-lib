# All-field port of `Langlands.Representation.Classification.ExponentFamily`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.ExponentFamily`. Original module: `Langlands.Representation.Classification.ExponentFamily`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/ExponentFamily.md`.

## Content

The exponent modulus and the family `π_s` of representations of `GL_n(F)` on one space of smooth functions, induced from the untwisted coefficient, whose member at `s` is equivalent to the normalized product with exponents `s u` (`exponentHeight`, `exponentFamilyEquiv`); the compact pairing between the members at `s` and `-s` (`normalizedIntegralForm_family_neg`) and the positive invariant form on the member at `0` (`familyZeroForm`).

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.PadicField.TopologicalData.exponentModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.exponentModulus` |
| `Langlands.PadicField.TopologicalData.coe_exponentModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.coe_exponentModulus` |
| `Langlands.PadicField.TopologicalData.exponentModulus_eq_one_of_mem` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.exponentModulus_eq_one_of_mem` |
| `Langlands.PadicField.TopologicalData.realPowerCharacter_exponentModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.realPowerCharacter_exponentModulus` |
| `Langlands.PadicField.TopologicalData.blockTensor_determinantTwist` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.blockTensor_determinantTwist` |
| `Langlands.PadicField.TopologicalData.realPowerTwist_exponentModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.realPowerTwist_exponentModulus` |
| `Langlands.PadicField.TopologicalData.exponentHeight` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.exponentHeight` |
| `Langlands.PadicField.TopologicalData.exponentHeight_modulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.exponentHeight_modulus` |
| `Langlands.PadicField.TopologicalData.exponentFamilyEquiv` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.exponentFamilyEquiv` |
| `Langlands.PadicField.TopologicalData.normalizedIntegralForm_family_neg` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedIntegralForm_family_neg` |
| `Langlands.PadicField.TopologicalData.familyZeroForm` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.familyZeroForm` |

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

The field-independent sesquilinear pairing declarations `Langlands.PadicField.TopologicalData.pairingSesquilinear`, `pairingSesquilinear_apply`, `pairingSesquilinear_invariant` and `pairingSesquilinear_ne_zero` are used unchanged. In `exponentModulus_eq_one_of_mem` the continuity of the determinant norm on each block is proved directly from the openness of its kernel (`isOpen_ker_determinantNorm`), instead of from the p-adic bundled continuous homomorphism `determinantNormContinuous`. The twist is `determinantPowerTwist` (see `LanglandsData`).

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
