# All-field port of `Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.TwoSupercuspidalBinaryProductBridge`. Original module: `Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge`; its mathematical content is
described in the Library file `Langlands/Representation/Classification/TwoSupercuspidalBinaryProductBridge.md`.

## Content

Comparisons between the all-rank binary normalized product `T.binaryNormalizedProductFunctor a b` and the two-block products: for positive ranks the binary product of `(A, B)` is the normalized product on `Shahidi.twoBlocks a c` of `twoBlockFactors A B`; products with a zero factor are zero; products with a one-dimensional factor on a rank-zero group are the rank cast of the other factor; the product of two one-dimensional rank-zero factors is one-dimensional.

The field is `F : Langlands.AllFieldBZ.LocalFieldPackage` (a field with no base field and no
characteristic hypothesis) and its local-field structure is `T : F.TopologicalData`, an
abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`. The module imports
the original module and uses its field-independent declarations directly. Each ported statement
is the original statement with the replacements listed under "Systematic changes", and each
proof is the original proof with the same replacements, except where listed below.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Classification.BinaryProductBridge.normalizedProductInductionFunctor_obj_congr` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.normalizedProductInductionFunctor_obj_congr` |
| `Langlands.Classification.BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks` |
| `Langlands.Classification.BinaryProductBridge.subsingleton_of_isZero` | `Langlands.AllFieldBZ.Derivative.ProductVanishing.subsingleton_of_isZero` |
| `Langlands.Classification.BinaryProductBridge.isZero_of_subsingleton` | `Langlands.AllFieldBZ.Derivative.ProductVanishing.isZero_of_subsingleton` |
| `Langlands.Classification.BinaryProductBridge.subsingleton_rankCast` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.subsingleton_rankCast` |
| `Langlands.Classification.BinaryProductBridge.subsingleton_rankCast_product` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.subsingleton_rankCast_product` |
| `Langlands.Classification.BinaryProductBridge.nonempty_iso_unit` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.nonempty_iso_unit` |
| `Langlands.Classification.BinaryProductBridge.rankCastEquiv` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.rankCastEquiv` |
| `Langlands.Classification.BinaryProductBridge.nonempty_equiv_rankCast_product_right` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.nonempty_equiv_rankCast_product_right` |
| `Langlands.Classification.BinaryProductBridge.nonempty_equiv_rankCast_product_left` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.nonempty_equiv_rankCast_product_left` |
| `Langlands.Classification.BinaryProductBridge.finrank_rankCast_product_of_zero_zero` | `Langlands.AllFieldBZ.Classification.BinaryProductBridge.finrank_rankCast_product_of_zero_zero` |

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

The field-independent shape identity `Langlands.Classification.BinaryProductBridge.binary_eq_twoBlocks` is used unchanged. The unit declarations come from `Langlands.AllFieldBZ.Representation.Induction.BinaryProductSupplement`.

## Use

This module is part of the all-field proof of Zelevinsky 1980, Proposition 1.11(b)
(reducibility of adjacent supercuspidal products), whose final theorem is
`Langlands.AllFieldBZ.Classification.adjacentSupercuspidalProductReducibility` in
`Langlands.AllFieldBZ.Representation.Classification.AdjacentSupercuspidalProductReducibilityProof`.
