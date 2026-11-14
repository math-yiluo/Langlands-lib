# All-field port of `Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof`. Original module: `Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/OrderedCuspidalProductNondegeneracyProof.md`.

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
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.generalLinearRankCast_comp_obj` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.generalLinearRankCast_comp_obj` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.generalLinearRankCast_symm_obj` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.generalLinearRankCast_symm_obj` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.generalLinearRankCast_map_injective` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.generalLinearRankCast_map_injective` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.mirabolicDerivativeOfOrder_rankCast_obj` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.mirabolicDerivativeOfOrder_rankCast_obj` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.finrank_generalLinearRankCast_top` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.finrank_generalLinearRankCast_top` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.exists_injective_of_rankCast` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.exists_injective_of_rankCast` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.Good` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.Good` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.good_of_iso` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.good_of_iso` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_top_of_good` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_top_of_good` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.level_of_good` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.level_of_good` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_subrepresentation_of_good` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_subrepresentation_of_good` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.hasNonzeroDerivative_eq_of_supercuspidal` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.hasNonzeroDerivative_eq_of_supercuspidal` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.good_of_supercuspidal` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.good_of_supercuspidal` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.good_universeLift_of_supercuspidal` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.good_universeLift_of_supercuspidal` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.binaryLineIso` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.binaryLineIso` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.finrank_graded_of_length_one` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.finrank_graded_of_length_one` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.finrank_generalLinearRankCast` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.finrank_generalLinearRankCast` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.finrank_binaryProduct_rank_zero` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.finrank_binaryProduct_rank_zero` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.finrank_generalLinearDerivative_order` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.finrank_generalLinearDerivative_order` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.finrank_topLeibnizPiece` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.finrank_topLeibnizPiece` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.finrank_top_binaryProduct` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.finrank_top_binaryProduct` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.binaryShapeIso` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.binaryShapeIso` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.headTailBridge` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.headTailBridge` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.HeadExclusion` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.HeadExclusion` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.caseTwo_false` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.caseTwo_false` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.good_step` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.good_step` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.singleFamily_eq` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.singleFamily_eq` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.singletonProductLiftIso` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.singletonProductLiftIso` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.supercuspidalProperty_transport` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.supercuspidalProperty_transport` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.good_single` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.good_single` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.Ordered` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.Ordered` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.headExclusion_of_ordered` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.headExclusion_of_ordered` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.ordered_tail` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.ordered_tail` |
| `Langlands.Derivative.OrderedCuspidalProductNondegeneracy.good_product` | `Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductNondegeneracy.good_product` |
| `Langlands.Derivative.orderedCuspidalProductNoDegenerateSubmodules` | `Langlands.AllFieldBZ.Derivative.orderedCuspidalProductNoDegenerateSubmodules` |

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
