# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPsiInduction`. Original module: `Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/MirabolicProductMinusLeftPsiInduction.md`.

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
| `Langlands.Derivative.MirabolicProductMinus.leftCharacter_radical` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftCharacter_radical` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiSection_determinantNorm` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiSection_determinantNorm` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiSection_character` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiSection_character` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiSection_halfModulus` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiSection_halfModulus` |
| `Langlands.Derivative.MirabolicProductMinus.leftCoefficientRadicalProjection` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftCoefficientRadicalProjection` |
| `Langlands.Derivative.MirabolicProductMinus.leftCoefficientRadicalProjection_surjective` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftCoefficientRadicalProjection_surjective` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficient` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficient` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficient_radical_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficient_radical_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficientOrdinaryEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficientOrdinaryEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficientEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficientEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficientEquiv_mk_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficientEquiv_mk_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficientEquiv_section_action` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficientEquiv_section_action` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiNormalizedCoefficient` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiNormalizedCoefficient` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiNormalizedCoefficient_action` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiNormalizedCoefficient_action` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficientMap` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficientMap` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiNormalizedCoefficientMap` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiNormalizedCoefficientMap` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficientEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficientEquiv_natural` |
| `Langlands.Derivative.MirabolicProductMinus.psiMinusOrdinaryEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.psiMinusOrdinaryEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.psiMinusOrdinaryEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.psiMinusOrdinaryEquiv_natural` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsi_mirabolic_compactOpenBasis` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsi_mirabolic_compactOpenBasis` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiCoefficient_isSmooth` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiCoefficient_isSmooth` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsi_normalSplitEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsi_normalSplitEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiInductionEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiInductionEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsi_normalSplitEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsi_normalSplitEquiv_natural` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiInductionEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiInductionEquiv_natural` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiZeroCoefficientEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiZeroCoefficientEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiZeroCoefficient_isSmooth` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiZeroCoefficient_isSmooth` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiZeroTensorEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiZeroTensorEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiZeroEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiZeroEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiZeroTensorEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiZeroTensorEquiv_natural` |
| `Langlands.Derivative.MirabolicProductMinus.leftPsiZeroEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPsiZeroEquiv_natural` |

## Private and anonymous declarations

Private helper declarations ported with the same short names: `leftIndex_first`, `leftIndex_second`, `leftPsi_det_lastRow`, `leftPsi_determinantNorm_projection`, `leftPsi_determinantNorm_radical`, `leftPsi_scalar_normalization`, `leftPsi_sqrt_div_pow`, `normalSplitCompactEquivOfKernel`, `normalSplitCompactEquivOfKernel_natural`, `compactInductionTwistEquiv_natural`.

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

## Build note

A Lake build of this module takes about 25 minutes. Almost all of it is spent after elaboration, when Lean writes the `.olean` file: Lean's sine-qua-non premise-selection index (`Lean.LibrarySuggestions.SineQuaNon`) then analyses the type of every theorem of the module, and this is slow for several of its theorems. The time affects no statement or proof.

## Provenance

Generated by the all-field port script of Worker 71 for the BZ77 mirabolic nondegeneracy task
(Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*, 1977, 4.9-4.11).
