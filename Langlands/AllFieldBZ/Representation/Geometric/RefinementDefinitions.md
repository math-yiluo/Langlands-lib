# All-field port of `Langlands.Representation.Geometric.RefinementDefinitions`

Lean module: `Langlands.AllFieldBZ.Representation.Geometric.RefinementDefinitions`. Original module: `Langlands.Representation.Geometric.RefinementDefinitions` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Geometric/RefinementDefinitions.md`.

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
| `Langlands.PadicField.TopologicalData.refinedLeviBlock` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviBlock` |
| `Langlands.PadicField.TopologicalData.refinedLeviModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviModulus` |
| `Langlands.PadicField.TopologicalData.refinedLeviModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviModulus_apply` |
| `Langlands.PadicField.TopologicalData.refinedParabolicModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicModulus` |
| `Langlands.PadicField.TopologicalData.refinedParabolicModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicModulus_apply` |
| `Langlands.PadicField.TopologicalData.refinedParabolicModulus_section` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicModulus_section` |
| `Langlands.PadicField.TopologicalData.refinedParabolicModulus_unipotent` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicModulus_unipotent` |
| `Langlands.PadicField.TopologicalData.refinedLeviHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviHalfModulus` |
| `Langlands.PadicField.TopologicalData.refinedLeviInverseHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviInverseHalfModulus` |
| `Langlands.PadicField.TopologicalData.refinedParabolicHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicHalfModulus` |
| `Langlands.PadicField.TopologicalData.refinedParabolicInverseHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicInverseHalfModulus` |
| `Langlands.PadicField.TopologicalData.refinedLeviHalfModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviHalfModulus_apply` |
| `Langlands.PadicField.TopologicalData.refinedLeviInverseHalfModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviInverseHalfModulus_apply` |
| `Langlands.PadicField.TopologicalData.refinedLeviHalfModulus_sq` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviHalfModulus_sq` |
| `Langlands.PadicField.TopologicalData.refinedLeviInverseHalfModulus_eq_inv` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviInverseHalfModulus_eq_inv` |
| `Langlands.PadicField.TopologicalData.refinedParabolicHalfModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicHalfModulus_apply` |
| `Langlands.PadicField.TopologicalData.refinedParabolicInverseHalfModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicInverseHalfModulus_apply` |
| `Langlands.PadicField.TopologicalData.refinedParabolicHalfModulus_section` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicHalfModulus_section` |
| `Langlands.PadicField.TopologicalData.refinedParabolicInverseHalfModulus_section` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicInverseHalfModulus_section` |
| `Langlands.PadicField.TopologicalData.refinedParabolicHalfModulus_unipotent` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicHalfModulus_unipotent` |
| `Langlands.PadicField.TopologicalData.refinedParabolicInverseHalfModulus_unipotent` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedParabolicInverseHalfModulus_unipotent` |
| `Langlands.PadicField.TopologicalData.refinedLeviHalfModulus_ker` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.refinedLeviHalfModulus_ker` |
| `Langlands.PadicField.TopologicalData.continuous_refinedLeviBlock` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.continuous_refinedLeviBlock` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_refinedLeviModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_refinedLeviModulus` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_refinedLeviHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_refinedLeviHalfModulus` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_refinedParabolicHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_refinedParabolicHalfModulus` |

## Private and anonymous declarations

Private helper declarations ported with the same short names: `block_mem_radical`.

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
