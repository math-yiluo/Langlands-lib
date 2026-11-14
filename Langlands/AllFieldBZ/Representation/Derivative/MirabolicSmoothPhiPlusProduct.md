# All-field port of `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.MirabolicSmoothPhiPlusProduct`. Original module: `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/MirabolicSmoothPhiPlusProduct.md`.

## Content

This module restates and reproves, over an arbitrary nonarchimedean local field, the
declarations of the original module whose statements or proofs depend on the p-adic field
package `Langlands.PadicField p`. The field is now `F : Langlands.AllFieldBZ.LocalFieldPackage`
(a field with no base field and no characteristic hypothesis), and its local-field structure is
`T : F.TopologicalData`, an abbreviation of the Library structure `Langlands.LocalFieldData F.Carrier`.
Declarations of the original module that do not depend on the field are not duplicated: the module
imports the original and uses them directly. Each ported statement is the original statement with the
replacements listed under "Systematic changes"; each proof is the original proof with the same
replacements.

## Ported declarations

| Original declaration | All-field declaration |
| --- | --- |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalAt` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalAt` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalAt_apply` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalAt_apply` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalAt_action` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalAt_action` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalAt_one_successor` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalAt_one_successor` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalAt_one_radical` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalAt_one_radical` |
| `Langlands.Derivative.Mirabolic.lTensor_evalAt_one_map_successor` | `Langlands.AllFieldBZ.Derivative.Mirabolic.lTensor_evalAt_one_map_successor` |
| `Langlands.Derivative.Mirabolic.lTensor_evalAt_one_map_radical` | `Langlands.AllFieldBZ.Derivative.Mirabolic.lTensor_evalAt_one_map_radical` |
| `Langlands.Derivative.Mirabolic.lTensor_evalAt_one_map` | `Langlands.AllFieldBZ.Derivative.Mirabolic.lTensor_evalAt_one_map` |
| `Langlands.Derivative.Mirabolic.phiMinusCharacter_mul_leftLeviCharacter_successor` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusCharacter_mul_leftLeviCharacter_successor` |
| `Langlands.Derivative.Mirabolic.leftMixedEval_successor_mul` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftMixedEval_successor_mul` |
| `Langlands.Derivative.Mirabolic.leftPhiHatSource` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatSource` |
| `Langlands.Derivative.Mirabolic.leftPhiHatValue` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatValue` |
| `Langlands.Derivative.Mirabolic.leftPhiHatValue_apply` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatValue_apply` |
| `Langlands.Derivative.Mirabolic.leftPhiHatValue_covariant_aux` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatValue_covariant_aux` |
| `Langlands.Derivative.Mirabolic.leftPhiHatValue_covariant` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatValue_covariant` |
| `Langlands.Derivative.Mirabolic.leftLeviCharacter_leftRadical` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftLeviCharacter_leftRadical` |
| `Langlands.Derivative.Mirabolic.leftPhiHatValue_radical` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatValue_radical` |
| `Langlands.Derivative.Mirabolic.leftPhiHatValue_exists_openSubgroup` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatValue_exists_openSubgroup` |
| `Langlands.Derivative.Mirabolic.leftPhiHatValue_isCompact` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatValue_isCompact` |
| `Langlands.Derivative.Mirabolic.leftPhiHatMap` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatMap` |
| `Langlands.Derivative.Mirabolic.leftPhiHatMap_eval` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatMap_eval` |
| `Langlands.Derivative.Mirabolic.leftPhiHatMap_radical` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatMap_radical` |
| `Langlands.Derivative.Mirabolic.leftPhiHatMap_successor` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatMap_successor` |
| `Langlands.Derivative.Mirabolic.leftPhiHatDescent` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatDescent` |
| `Langlands.Derivative.Mirabolic.leftPhiHatEmbedding` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatEmbedding` |
| `Langlands.Derivative.Mirabolic.leftPhiHatEmbedding_eval` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatEmbedding_eval` |
| `Langlands.Derivative.Mirabolic.leftPhiHatSource_eq_zero` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatSource_eq_zero` |
| `Langlands.Derivative.Mirabolic.leftPhiHatEmbedding_injective` | `Langlands.AllFieldBZ.Derivative.Mirabolic.leftPhiHatEmbedding_injective` |

## Systematic changes

- `Langlands.PadicField.{u} p` becomes `Langlands.AllFieldBZ.LocalFieldPackage.{u}`; the prime
  `p` and its `Fact p.Prime` instance are removed from binders, and the corresponding explicit
  arguments are dropped.
- Normalization API names on `T` (for example `Integers`, `ord`, `normalizedAbs`, `uniformizer`)
  resolve to `Langlands.LocalFieldData`; the remaining p-adic foundation facts are replaced by the
  arbitrary-field versions in `Langlands.AllFieldBZ.LocalField.Definitions`.
- Every ported declaration `Langlands.X` is renamed `Langlands.AllFieldBZ.X` (with `PadicField`
  replaced by `LocalFieldPackage` in the name); a declaration in a namespace outside `Langlands`
  is renamed `<original name>_allFieldBZ`. References to ported declarations are renamed accordingly.
- The original namespaces are opened, hiding the names that have ported versions, so that unported
  field-independent declarations are used unchanged.

## Provenance

Generated by the all-field port script of Worker 71 for the BZ77 mirabolic nondegeneracy task
(Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*, 1977, 4.9-4.11).
