# All-field port of `Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof`. Original module: `Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/TwoBlockExponentNonUnitarizabilityProof.md`.

## Content

`twoBlockLargeExponentNonUnitarizable` proves `TwoBlockLargeExponentNonUnitarizable` over every nonarchimedean local field: a vector of the induced representation built from a block Iwahori factorization has a matrix coefficient that grows along the powers of a weakly contracting block scalar, so no invariant positive form exists (`not_isUnitarizable_normalizedParabolicInduced`).

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.TwoBlockExponentNonUnitarizability.exists_mul_blockScalar_pow` | `Langlands.AllFieldBZ.Classification.TwoBlockExponentNonUnitarizability.exists_mul_blockScalar_pow` |
| `Langlands.Classification.TwoBlockExponentNonUnitarizability.not_isUnitarizable_normalizedParabolicInduced` | `Langlands.AllFieldBZ.Classification.TwoBlockExponentNonUnitarizability.not_isUnitarizable_normalizedParabolicInduced` |
| `Langlands.Classification.TwoBlockExponentNonUnitarizability.exists_segmentFactor_scalar_eigen` | `Langlands.AllFieldBZ.Classification.TwoBlockExponentNonUnitarizability.exists_segmentFactor_scalar_eigen` |
| `Langlands.Classification.twoBlockLargeExponentNonUnitarizable` | `Langlands.AllFieldBZ.Classification.twoBlockLargeExponentNonUnitarizable` |

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

The field-independent declarations of the sections `Bounded`, `Average` and `Abstract` of the original, and `leviSubgroup_le_parabolic`, `unipotentSubgroup_le_parabolic` and `exists_dual_tprod_eq_one`, are used unchanged. The block Iwahori predicates are the all-field `Langlands.GeneralLinear.BlockShape.HasBlockIwahoriFactorization_allFieldBZ` and `IsWeaklyContracting_allFieldBZ`. The norm of `|det|^s` at scalars comes from `Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwistSupplement`, and the block modulus of `Shahidi.twoBlocks` from `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviModulus_twoBlocks`.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
