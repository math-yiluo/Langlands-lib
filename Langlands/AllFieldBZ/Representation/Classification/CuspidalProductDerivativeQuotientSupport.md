# All-field port of `Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport`

Lean module: `Langlands.AllFieldBZ.Representation.Classification.CuspidalProductDerivativeQuotientSupport`. Original module: `Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Classification/CuspidalProductDerivativeQuotientSupport.md`.

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
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.intersectionTransportEquivTo` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.intersectionTransportEquivTo` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.normalizedRefinedInducedCongr` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.normalizedRefinedInducedCongr` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.fullSourcePieceEquiv` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.fullSourcePieceEquiv` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.supercuspidalProperty_cast` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.supercuspidalProperty_cast` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.castSupercuspidal` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.castSupercuspidal` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.cuspidalDatum_castSupercuspidal` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.cuspidalDatum_castSupercuspidal` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.innerFactor` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.innerFactor` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.flattenedLeviProductEquiv_flattenedLeviEquiv_symm` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.flattenedLeviProductEquiv_flattenedLeviEquiv_symm` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.inducingEquiv` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.inducingEquiv` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.exists_inner_factors` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.exists_inner_factors` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.isQuotient_first_block` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.isQuotient_first_block` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.full_piece_quotient` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.full_piece_quotient` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.isSubquotient_cuspidalProductInduced` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.isSubquotient_cuspidalProductInduced` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.full_piece_support` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.full_piece_support` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.jacquet_quotient_support` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.jacquet_quotient_support` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.exists_rankCast_map` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.exists_rankCast_map` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.isCuspidalConstituent_of_rankCast` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.isCuspidalConstituent_of_rankCast` |
| `Langlands.Classification.CuspidalProductDerivativeQuotientSupport.derivative_quotient_support` | `Langlands.AllFieldBZ.Classification.CuspidalProductDerivativeQuotientSupport.derivative_quotient_support` |

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
