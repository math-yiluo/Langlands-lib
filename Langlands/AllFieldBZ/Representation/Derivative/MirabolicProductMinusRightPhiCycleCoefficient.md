# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient`. Original module: `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/MirabolicProductMinusRightPhiCycleCoefficient.md`.

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
| `Langlands.Derivative.MirabolicProductMinus.rightPsiKernelCharacter` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiKernelCharacter` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiLocalizedTensor_comp` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiLocalizedTensor_comp` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiLocalizedTensorForward` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiLocalizedTensorForward` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiLocalizedTensorBilinear` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiLocalizedTensorBilinear` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiLocalizedTensorEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiLocalizedTensorEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.rightPsiLocalizedTensorEquiv_mk_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightPsiLocalizedTensorEquiv_mk_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleIntersectionToKernel` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleIntersectionToKernel` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleKernelToIntersection` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleKernelToIntersection` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleCoefficient` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleCoefficient` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleStagesCoefficient` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleStagesCoefficient` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycle_relations_eq` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycle_relations_eq` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv_mk_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv_mk_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv_section` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv_section` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv_natural_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv_natural_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycleCoefficientEquiv_natural` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycle_phiMinus_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycle_phiMinus_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.determinantNorm_val_eq_projection` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.determinantNorm_val_eq_projection` |
| `Langlands.Derivative.MirabolicProductMinus.rightCycle_scalar_eq` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.rightCycle_scalar_eq` |

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
