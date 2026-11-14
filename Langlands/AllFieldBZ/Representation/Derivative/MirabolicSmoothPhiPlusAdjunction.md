# All-field port of `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`. Original module: `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/MirabolicSmoothPhiPlusAdjunction.md`.

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
| `Langlands.Derivative.Mirabolic.phiMinusCharacter_mul_phiPlusCharacter_apply` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusCharacter_mul_phiPlusCharacter_apply` |
| `Langlands.Derivative.Mirabolic.psiMinusCharacter_mul_psiPlusCharacter_apply` | `Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusCharacter_mul_psiPlusCharacter_apply` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalOne` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalOne` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalOne_apply` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalOne_apply` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalOne_translate` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalOne_translate` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalOne_radical` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalOne_radical` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalOne_successor` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalOne_successor` |
| `Langlands.Derivative.Mirabolic.phiHatPlusEvalOne_phiMinus_action` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusEvalOne_phiMinus_action` |
| `Langlands.Derivative.Mirabolic.phiHatPlusAdjForward` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusAdjForward` |
| `Langlands.Derivative.Mirabolic.phiHatPlusAdjForward_mk` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusAdjForward_mk` |
| `Langlands.Derivative.Mirabolic.phiMinusAdjValue` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusAdjValue` |
| `Langlands.Derivative.Mirabolic.phiMinusAdjValue_apply` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusAdjValue_apply` |
| `Langlands.Derivative.Mirabolic.phiMinusAdjValue_radical` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusAdjValue_radical` |
| `Langlands.Derivative.Mirabolic.phiMinusAdjValue_successor` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusAdjValue_successor` |
| `Langlands.Derivative.Mirabolic.phiMinusAdjValue_covariant` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusAdjValue_covariant` |
| `Langlands.Derivative.Mirabolic.phiHatPlusOrbitMap` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusOrbitMap` |
| `Langlands.Derivative.Mirabolic.phiHatPlusAdjBackward` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusAdjBackward` |
| `Langlands.Derivative.Mirabolic.phiHatPlusAdjBackward_eval` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusAdjBackward_eval` |
| `Langlands.Derivative.Mirabolic.phiHatPlusAdjunction` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusAdjunction` |
| `Langlands.Derivative.Mirabolic.phiHatPlusAdjunction_comp_left` | `Langlands.AllFieldBZ.Derivative.Mirabolic.phiHatPlusAdjunction_comp_left` |
| `Langlands.Derivative.Mirabolic.psiPlusAdj_radical` | `Langlands.AllFieldBZ.Derivative.Mirabolic.psiPlusAdj_radical` |
| `Langlands.Derivative.Mirabolic.psiPlusAdjForward` | `Langlands.AllFieldBZ.Derivative.Mirabolic.psiPlusAdjForward` |
| `Langlands.Derivative.Mirabolic.psiPlusAdjBackward` | `Langlands.AllFieldBZ.Derivative.Mirabolic.psiPlusAdjBackward` |
| `Langlands.Derivative.Mirabolic.psiPlusAdjunction` | `Langlands.AllFieldBZ.Derivative.Mirabolic.psiPlusAdjunction` |
| `Langlands.Derivative.Mirabolic.psiPlusAdjunction_comp_left` | `Langlands.AllFieldBZ.Derivative.Mirabolic.psiPlusAdjunction_comp_left` |

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
