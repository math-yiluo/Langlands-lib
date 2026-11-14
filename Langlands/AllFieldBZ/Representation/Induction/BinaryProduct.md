# All-field port of `Langlands.Representation.Induction.BinaryProduct`

Lean module: `Langlands.AllFieldBZ.Representation.Induction.BinaryProduct`. Original module: `Langlands.Representation.Induction.BinaryProduct` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Induction/BinaryProduct.md`.

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
| `Langlands.PadicField.TopologicalData.normalizedProductInducedMap_eq_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedProductInducedMap_eq_zero` |
| `Langlands.PadicField.TopologicalData.binaryPairFamilyFunctor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPairFamilyFunctor` |
| `Langlands.PadicField.TopologicalData.binaryPositiveProductFunctor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPositiveProductFunctor` |
| `Langlands.PadicField.TopologicalData.binaryPositiveProductFunctor_map` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPositiveProductFunctor_map` |
| `Langlands.PadicField.TopologicalData.binaryLeftZeroTensorObj` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorObj` |
| `Langlands.PadicField.TopologicalData.binaryLeftZeroTensorFunctor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorFunctor` |
| `Langlands.PadicField.TopologicalData.binaryLeftZeroTensorFunctor_map` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorFunctor_map` |
| `Langlands.PadicField.TopologicalData.binaryRightZeroTensorObj` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorObj` |
| `Langlands.PadicField.TopologicalData.binaryRightZeroTensorFunctor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorFunctor` |
| `Langlands.PadicField.TopologicalData.binaryRightZeroTensorFunctor_map` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorFunctor_map` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductFunctor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductFunctor_zero_left` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor_zero_left` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductFunctor_of_left_eq_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor_of_left_eq_zero` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductFunctor_of_right_eq_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor_of_right_eq_zero` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductFunctor_of_pos` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor_of_pos` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductLeftZeroIso` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductLeftZeroIso` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductRightZeroIso` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductRightZeroIso` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductPositiveIso` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductPositiveIso` |
| `Langlands.PadicField.TopologicalData.binaryLeftZeroTensorEquiv` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorEquiv` |
| `Langlands.PadicField.TopologicalData.binaryLeftZeroTensorEquiv_naturality` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorEquiv_naturality` |
| `Langlands.PadicField.TopologicalData.binaryZeroZeroTensorEquiv` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryZeroZeroTensorEquiv` |
| `Langlands.PadicField.TopologicalData.binaryZeroZeroTensorEquiv_naturality` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryZeroZeroTensorEquiv_naturality` |
| `Langlands.PadicField.TopologicalData.binaryRightZeroTensorEquiv` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorEquiv` |
| `Langlands.PadicField.TopologicalData.binaryRightZeroTensorEquiv_naturality` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorEquiv_naturality` |
| `Langlands.PadicField.TopologicalData.binaryLeftZeroTensorFunctor_map_eq_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryLeftZeroTensorFunctor_map_eq_zero` |
| `Langlands.PadicField.TopologicalData.binaryRightZeroTensorFunctor_map_eq_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryRightZeroTensorFunctor_map_eq_zero` |
| `Langlands.PadicField.TopologicalData.binaryPositiveProductFunctor_map_eq_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryPositiveProductFunctor_map_eq_zero` |
| `Langlands.PadicField.TopologicalData.binaryNormalizedProductFunctor_map_eq_zero` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.binaryNormalizedProductFunctor_map_eq_zero` |
| `Langlands.PadicField.TopologicalData.isZero_binaryNormalizedProductFunctor_obj` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isZero_binaryNormalizedProductFunctor_obj` |

## Private and anonymous declarations

Private helper declarations ported with the same short names: `smoothRep_hom_zero`, `smoothRep_eq_zero`, `map_eq_zero_of_iso`.

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
