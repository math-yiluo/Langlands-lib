# All-field port of `Langlands.Group.GL.BlockModulus`

Lean module: `Langlands.AllFieldBZ.Group.GL.BlockModulus`. Original module: `Langlands.Group.GL.BlockModulus` in the Library; its mathematical
content is described in the Library file `Langlands/Group/GL/BlockModulus.md`.

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
| `Langlands.PadicField.TopologicalData.blockDeterminantNorm` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.blockDeterminantNorm` |
| `Langlands.PadicField.TopologicalData.blockDeterminantNorm_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.blockDeterminantNorm_apply` |
| `Langlands.PadicField.TopologicalData.leviModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviModulus` |
| `Langlands.PadicField.TopologicalData.leviModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviModulus_apply` |
| `Langlands.PadicField.TopologicalData.parabolicModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicModulus` |
| `Langlands.PadicField.TopologicalData.parabolicModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicModulus_apply` |
| `Langlands.PadicField.TopologicalData.parabolicModulus_section` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicModulus_section` |
| `Langlands.PadicField.TopologicalData.parabolicModulus_unipotent` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicModulus_unipotent` |
| `Langlands.PadicField.TopologicalData.normOneLevi` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normOneLevi` |
| `Langlands.PadicField.TopologicalData.mem_normOneLevi` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.mem_normOneLevi` |
| `Langlands.PadicField.TopologicalData.normOneLevi_le_ker_leviModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.normOneLevi_le_ker_leviModulus` |
| `Langlands.PadicField.TopologicalData.isOpen_normOneLevi` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_normOneLevi` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_leviModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_leviModulus` |
| `Langlands.PadicField.TopologicalData.leviModulus_scalar` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviModulus_scalar` |
| `Langlands.PadicField.TopologicalData.leviHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus` |
| `Langlands.PadicField.TopologicalData.leviHalfModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus_apply` |
| `Langlands.PadicField.TopologicalData.leviHalfModulus_sq` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus_sq` |
| `Langlands.PadicField.TopologicalData.leviHalfModulus_eq_one` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus_eq_one` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_leviHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_leviHalfModulus` |
| `Langlands.PadicField.TopologicalData.parabolicHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicHalfModulus` |
| `Langlands.PadicField.TopologicalData.parabolicHalfModulus_apply` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicHalfModulus_apply` |
| `Langlands.PadicField.TopologicalData.parabolicHalfModulus_section` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicHalfModulus_section` |
| `Langlands.PadicField.TopologicalData.parabolicHalfModulus_unipotent` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.parabolicHalfModulus_unipotent` |
| `Langlands.PadicField.TopologicalData.isOpen_ker_parabolicHalfModulus` | `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.isOpen_ker_parabolicHalfModulus` |

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
