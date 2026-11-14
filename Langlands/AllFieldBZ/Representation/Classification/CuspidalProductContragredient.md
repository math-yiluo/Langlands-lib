# All-field port of `Langlands.Representation.Classification.CuspidalProductContragredient`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.CuspidalProductContragredient`. Original module: `Langlands.Representation.Classification.CuspidalProductContragredient` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Classification/CuspidalProductContragredient.md`.

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
| `Langlands.Classification.CuspidalProductContragredient.dualClass` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualClass` |
| `Langlands.Classification.CuspidalProductContragredient.dualClass_def` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualClass_def` |
| `Langlands.Classification.CuspidalProductContragredient.dualDatum` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualDatum` |
| `Langlands.Classification.CuspidalProductContragredient.dualDatum_rank` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualDatum_rank` |
| `Langlands.Classification.CuspidalProductContragredient.dualDatum_cls` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualDatum_cls` |
| `Langlands.Classification.CuspidalProductContragredient.dualDatum_dualDatum` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualDatum_dualDatum` |
| `Langlands.Classification.CuspidalProductContragredient.classContragredient_realPowerTwist` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.classContragredient_realPowerTwist` |
| `Langlands.Classification.CuspidalProductContragredient.dualDatum_twist` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualDatum_twist` |
| `Langlands.Classification.CuspidalProductContragredient.twistedDualData` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twistedDualData` |
| `Langlands.Classification.CuspidalProductContragredient.ofFn_twistedDualData` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.ofFn_twistedDualData` |
| `Langlands.Classification.CuspidalProductContragredient.twist_le_of_dual_le` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twist_le_of_dual_le` |
| `Langlands.Classification.CuspidalProductContragredient.determinantPowerCharacter_leviEmbedding` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.determinantPowerCharacter_leviEmbedding` |
| `Langlands.Classification.CuspidalProductContragredient.determinantPowerCharacter_parabolic` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.determinantPowerCharacter_parabolic` |
| `Langlands.Classification.CuspidalProductContragredient.nonempty_twist_productEquiv` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.nonempty_twist_productEquiv` |
| `Langlands.Classification.CuspidalProductContragredient.nonempty_contragredient_productEquiv` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.nonempty_contragredient_productEquiv` |
| `Langlands.Classification.CuspidalProductContragredient.dualRep` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualRep` |
| `Langlands.Classification.CuspidalProductContragredient.dualRep_obj` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualRep_obj` |
| `Langlands.Classification.CuspidalProductContragredient.twistedDualRep` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twistedDualRep` |
| `Langlands.Classification.CuspidalProductContragredient.dualRep_represents` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.dualRep_represents` |
| `Langlands.Classification.CuspidalProductContragredient.twistedDualRep_represents` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.twistedDualRep_represents` |
| `Langlands.Classification.CuspidalProductContragredient.cuspidalProductInduced_dualDatum` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.cuspidalProductInduced_dualDatum` |
| `Langlands.Classification.CuspidalProductContragredient.cuspidalProductInduced_twistedDualData` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.cuspidalProductInduced_twistedDualData` |
| `Langlands.Classification.CuspidalProductContragredient.nonempty_contragredient_cuspidalProductIso` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.nonempty_contragredient_cuspidalProductIso` |
| `Langlands.Classification.CuspidalProductContragredient.nonempty_twistedDual_cuspidalProductEquiv` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.nonempty_twistedDual_cuspidalProductEquiv` |
| `Langlands.Classification.CuspidalProductContragredient.isCuspidalConstituent_contragredient` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.isCuspidalConstituent_contragredient` |
| `Langlands.Classification.CuspidalProductContragredient.isSupercuspidalSupport_contragredient` | `Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.isSupercuspidalSupport_contragredient` |

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
