# All-field port of `Langlands.Representation.Derivative.RightMixedProductDerivativePositive`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.RightMixedProductDerivativePositive`. Original module: `Langlands.Representation.Derivative.RightMixedProductDerivativePositive` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/RightMixedProductDerivativePositive.md`.

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
| `Langlands.Derivative.RightMixedDerivative.mapsShortExact_generalLinearRankCast` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.mapsShortExact_generalLinearRankCast` |
| `Langlands.Derivative.RightMixedDerivative.derivative_transport` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.derivative_transport` |
| `Langlands.Derivative.RightMixedDerivative.castDerivativeCast_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.castDerivativeCast_eq` |
| `Langlands.Derivative.RightMixedDerivative.phiMinus_derivative_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.phiMinus_derivative_eq` |
| `Langlands.Derivative.RightMixedDerivative.derivative_succ_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.derivative_succ_eq` |
| `Langlands.Derivative.RightMixedDerivative.restrictionDerivative_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.restrictionDerivative_eq` |
| `Langlands.Derivative.RightMixedDerivative.pieceShift_aux` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.pieceShift_aux` |
| `Langlands.Derivative.RightMixedDerivative.glued_rankCast` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.glued_rankCast` |
| `Langlands.Derivative.RightMixedDerivative.source_eq_comp` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.source_eq_comp` |
| `Langlands.Derivative.RightMixedDerivative.piece_eq_comp` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.piece_eq_comp` |
| `Langlands.Derivative.RightMixedDerivative.source_succ_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.source_succ_eq` |
| `Langlands.Derivative.RightMixedDerivative.quotient_eq₁` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.quotient_eq₁` |
| `Langlands.Derivative.RightMixedDerivative.quotient_eq₂` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.quotient_eq₂` |
| `Langlands.Derivative.RightMixedDerivative.quotientIso` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.quotientIso` |
| `Langlands.Derivative.RightMixedDerivative.derivativeCast_subsingleton` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.derivativeCast_subsingleton` |
| `Langlands.Derivative.RightMixedDerivative.quotient_subsingleton` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.quotient_subsingleton` |
| `Langlands.Derivative.RightMixedDerivative.sub_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.sub_eq` |
| `Langlands.Derivative.RightMixedDerivative.pieceShift_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.pieceShift_eq` |
| `Langlands.Derivative.RightMixedDerivative.source_one_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.source_one_eq` |
| `Langlands.Derivative.RightMixedDerivative.piece_one_eq` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.piece_one_eq` |
| `Langlands.Derivative.RightMixedDerivative.glued_one` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.glued_one` |
| `Langlands.Derivative.RightMixedDerivative.glued_zero` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.glued_zero` |
| `Langlands.Derivative.RightMixedDerivative.glued_succ` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.glued_succ` |
| `Langlands.Derivative.RightMixedDerivative.glued_pos` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.glued_pos` |
| `Langlands.Derivative.RightMixedDerivative.filtration_pos` | `Langlands.AllFieldBZ.Derivative.RightMixedDerivative.filtration_pos` |

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
