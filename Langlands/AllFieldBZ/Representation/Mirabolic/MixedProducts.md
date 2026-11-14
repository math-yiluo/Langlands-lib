# All-field port of `Langlands.Representation.Mirabolic.MixedProducts`

Lean module: `Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts`. Original module: `Langlands.Representation.Mirabolic.MixedProducts` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Mirabolic/MixedProducts.md`.

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
| `Langlands.PadicField.TopologicalData.leftLeviCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftLeviCharacter` |
| `Langlands.PadicField.TopologicalData.leftLeviCharacter_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftLeviCharacter_apply` |
| `Langlands.PadicField.TopologicalData.rightLeviCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightLeviCharacter` |
| `Langlands.PadicField.TopologicalData.rightLeviCharacter_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightLeviCharacter_apply` |
| `Langlands.PadicField.TopologicalData.leftLeviCharacter_zero_left` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftLeviCharacter_zero_left` |
| `Langlands.PadicField.TopologicalData.rightLeviCharacter_zero_left` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightLeviCharacter_zero_left` |
| `Langlands.PadicField.TopologicalData.rightLeviCharacter_zero_right_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightLeviCharacter_zero_right_apply` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_leftLeviCharacter_comp` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_leftLeviCharacter_comp` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_rightLeviCharacter_comp` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_rightLeviCharacter_comp` |
| `Langlands.PadicField.TopologicalData.leftCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftCharacter` |
| `Langlands.PadicField.TopologicalData.rightCharacter` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightCharacter` |
| `Langlands.PadicField.TopologicalData.leftCharacter_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftCharacter_apply` |
| `Langlands.PadicField.TopologicalData.rightCharacter_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightCharacter_apply` |
| `Langlands.PadicField.TopologicalData.leftCharacter_zero_left` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftCharacter_zero_left` |
| `Langlands.PadicField.TopologicalData.rightCharacter_zero_left` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightCharacter_zero_left` |
| `Langlands.PadicField.TopologicalData.leftMixedProductFunctor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedProductFunctor` |
| `Langlands.PadicField.TopologicalData.rightMixedProductFunctor` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightMixedProductFunctor` |
| `Langlands.PadicField.TopologicalData.leftMixedEval` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedEval` |
| `Langlands.PadicField.TopologicalData.rightMixedEval` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightMixedEval` |
| `Langlands.PadicField.TopologicalData.leftMixedEval_injective` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedEval_injective` |
| `Langlands.PadicField.TopologicalData.rightMixedEval_injective` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightMixedEval_injective` |
| `Langlands.PadicField.TopologicalData.leftMixedEval_covariant` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedEval_covariant` |
| `Langlands.PadicField.TopologicalData.leftMixedEval_leftMatrix_mul` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedEval_leftMatrix_mul` |
| `Langlands.PadicField.TopologicalData.leftMixedEval_of_mem_leftKernel_mul` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedEval_of_mem_leftKernel_mul` |
| `Langlands.PadicField.TopologicalData.leftMixedProductFunctor_action` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedProductFunctor_action` |
| `Langlands.PadicField.TopologicalData.leftMixedEval_exists_openSubgroup` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedEval_exists_openSubgroup` |
| `Langlands.PadicField.TopologicalData.rightMixedEval_isCompact_quotientSupport` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.rightMixedEval_isCompact_quotientSupport` |
| `Langlands.PadicField.TopologicalData.leftMixedMk` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leftMixedMk` |

## Private and anonymous declarations

Private helper declarations ported with the same short names: `subsingleton_leftQuotient`, `determinantNorm_zero`.

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
