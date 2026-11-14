# All-field port of `Langlands.Representation.Classification.SupercuspidalTopDerivative`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTopDerivative`. Original module: `Langlands.Representation.Classification.SupercuspidalTopDerivative` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Classification/SupercuspidalTopDerivative.md`.

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
| `Langlands.Classification.SupercuspidalTopDerivative.phiMinusCharacter_eq_one_of_upper` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.phiMinusCharacter_eq_one_of_upper` |
| `Langlands.Classification.SupercuspidalTopDerivative.phiMinusQuotient_eq_of_eq_radical_mul_successor` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.phiMinusQuotient_eq_of_eq_radical_mul_successor` |
| `Langlands.Classification.SupercuspidalTopDerivative.psiMinusQuotient_iterateQuotient_upper` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.psiMinusQuotient_iterateQuotient_upper` |
| `Langlands.Classification.SupercuspidalTopDerivative.topQuotient` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.topQuotient` |
| `Langlands.Classification.SupercuspidalTopDerivative.topQuotient_surjective` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.topQuotient_surjective` |
| `Langlands.Classification.SupercuspidalTopDerivative.comp_topQuotient_mem_glFunctionals` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.comp_topQuotient_mem_glFunctionals` |
| `Langlands.Classification.SupercuspidalTopDerivative.phiMinus_obj_heq` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.phiMinus_obj_heq` |
| `Langlands.Classification.SupercuspidalTopDerivative.phiMinusIterate_obj_succ_bottom` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.phiMinusIterate_obj_succ_bottom` |
| `Langlands.Classification.SupercuspidalTopDerivative.generalLinearRestriction_rankCast_heq` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.generalLinearRestriction_rankCast_heq` |
| `Langlands.Classification.SupercuspidalTopDerivative.nontrivial_rankCast` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.nontrivial_rankCast` |
| `Langlands.Classification.SupercuspidalTopDerivative.isIrreducible_rankCast` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.isIrreducible_rankCast` |
| `Langlands.Classification.SupercuspidalTopDerivative.nontrivial_phiMinusIterate` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.nontrivial_phiMinusIterate` |
| `Langlands.Classification.SupercuspidalTopDerivative.psiMinusQuotient_zero_injective` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.psiMinusQuotient_zero_injective` |
| `Langlands.Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivativePositive_top` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivativePositive_top` |
| `Langlands.Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivative_top` | `Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivative_top` |

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
