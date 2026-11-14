# All-field port of `Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.PartialDerivativeJacquetNormalization`. Original module: `Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/PartialDerivativeJacquetNormalization.md`.

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
| `Langlands.Derivative.JacquetNormalization.determinantNorm_levi` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.determinantNorm_levi` |
| `Langlands.Derivative.JacquetNormalization.determinantNorm_successorIterate` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.determinantNorm_successorIterate` |
| `Langlands.Derivative.JacquetNormalization.phiMinusCharacter_successorIterate` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiMinusCharacter_successorIterate` |
| `Langlands.Derivative.JacquetNormalization.phiMinusCharacter_levi` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiMinusCharacter_levi` |
| `Langlands.Derivative.JacquetNormalization.psiMinusCharacter_eq_inverseHalf` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.psiMinusCharacter_eq_inverseHalf` |
| `Langlands.Derivative.JacquetNormalization.leviModulus_first` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.leviModulus_first` |
| `Langlands.Derivative.JacquetNormalization.inverseHalf_leviModulus_first` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.inverseHalf_leviModulus_first` |
| `Langlands.Derivative.JacquetNormalization.phiStepMk` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiStepMk` |
| `Langlands.Derivative.JacquetNormalization.phiStepMk_surjective` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiStepMk_surjective` |
| `Langlands.Derivative.JacquetNormalization.phiStepMk_natural` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiStepMk_natural` |
| `Langlands.Derivative.JacquetNormalization.phiStep_action_mk` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiStep_action_mk` |
| `Langlands.Derivative.JacquetNormalization.phiIterateMk` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiIterateMk` |
| `Langlands.Derivative.JacquetNormalization.phiIterateMk_surjective` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiIterateMk_surjective` |
| `Langlands.Derivative.JacquetNormalization.phiIterateMk_natural` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiIterateMk_natural` |
| `Langlands.Derivative.JacquetNormalization.phiIterate_action_mk` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.phiIterate_action_mk` |
| `Langlands.Derivative.JacquetNormalization.mirabolicDerivativeMk` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.mirabolicDerivativeMk` |
| `Langlands.Derivative.JacquetNormalization.mirabolicDerivativeMk_surjective` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.mirabolicDerivativeMk_surjective` |
| `Langlands.Derivative.JacquetNormalization.mirabolicDerivativeMk_natural` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.mirabolicDerivativeMk_natural` |
| `Langlands.Derivative.JacquetNormalization.mirabolicDerivative_action_mk` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.mirabolicDerivative_action_mk` |
| `Langlands.Derivative.JacquetNormalization.generalLinearDerivativePositiveMk` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.generalLinearDerivativePositiveMk` |
| `Langlands.Derivative.JacquetNormalization.generalLinearDerivativePositiveMk_surjective` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.generalLinearDerivativePositiveMk_surjective` |
| `Langlands.Derivative.JacquetNormalization.generalLinearDerivativePositiveMk_natural` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.generalLinearDerivativePositiveMk_natural` |
| `Langlands.Derivative.JacquetNormalization.generalLinearDerivativePositive_action_mk` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.generalLinearDerivativePositive_action_mk` |
| `Langlands.Derivative.JacquetNormalization.generalLinearDerivativePositive_action_mk_eq_inverseHalf` | `Langlands.AllFieldBZ.Derivative.JacquetNormalization.generalLinearDerivativePositive_action_mk_eq_inverseHalf` |

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
