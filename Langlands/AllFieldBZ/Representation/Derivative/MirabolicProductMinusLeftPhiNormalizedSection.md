# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection`. Original module: `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/MirabolicProductMinusLeftPhiNormalizedSection.md`.

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
| `Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerCharacter` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiStabilizerCharacter` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiStabilizerCharacter_radical` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiStabilizerCharacter_radical` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStabilizer` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStabilizer` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStabilizer_radical` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStabilizer_radical` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesQuotient` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesQuotient` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedRadicalEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedRadicalEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedRadicalEquiv_mk` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedRadicalEquiv_mk` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv_mk` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv_mk` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiCharacter_rankCast_symm` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiCharacter_rankCast_symm` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiAmbientSectionCharacter` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiAmbientSectionCharacter` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesAction` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesAction` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv_action_mk` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv_action_mk` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedSection_scalar` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedSection_scalar` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv_one_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv_one_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesQuotient_zero_subsingleton` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesQuotient_zero_subsingleton` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesTensorEquiv` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesTensorEquiv` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesTensorEquiv_mk_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesTensorEquiv_mk_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesTensorEquiv_action_tmul` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesTensorEquiv_action_tmul` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStabilizerMap` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStabilizerMap` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesMap` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesMap` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesMap_mk` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesMap_mk` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesCoefficientEquiv_natural` |
| `Langlands.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesTensorEquiv_natural` | `Langlands.AllFieldBZ.Derivative.MirabolicProductMinus.leftPhiNormalizedStagesTensorEquiv_natural` |

## Private and anonymous declarations

Private helper declarations ported with the same short names: `leftPhi_radical_determinantNorm`.

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
