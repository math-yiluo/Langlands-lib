# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient`. Original module: `Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/MirabolicProductMinusRightPsiCoefficient.md`.

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
| `Langlands.Derivative.MirabolicProductMinus.rightPsiInducingCoefficient` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiInducingCoefficient` |
| `Langlands.Derivative.MirabolicProductMinus.rightCharacter_of_mem_rightPsiKernel` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCharacter_of_mem_rightPsiKernel` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiInducingCoefficient_kernel` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiInducingCoefficient_kernel` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiTensorForward` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiTensorForward` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiTensorBilinear` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiTensorBilinear` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiTensorEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiTensorEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiTensorEquiv_mk_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiTensorEquiv_mk_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.leviModulus_binary` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leviModulus_binary` |
| `Langlands.Derivative.MirabolicProductMinus.parabolicHalfModulus_binary` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.parabolicHalfModulus_binary` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiStagesCoefficient` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiStagesCoefficient` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_mk_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_mk_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_section` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_section` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_psiMinus` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_psiMinus` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsi_scalar_eq` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsi_scalar_eq` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_action_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_action_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_action` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_action` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_natural_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_natural_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiCoefficientEquiv_natural` |

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
