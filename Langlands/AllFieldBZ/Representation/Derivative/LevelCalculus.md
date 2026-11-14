# All-field port of `Langlands.Representation.Derivative.LevelCalculus`

Lean module: `Langlands.AllFieldBZ.Representation.Derivative.LevelCalculus`. Original module: `Langlands.Representation.Derivative.LevelCalculus` in the Library; its mathematical
content is described in the Library file `Langlands/Representation/Derivative/LevelCalculus.md`.

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
| `Langlands.Derivative.LevelCalculus.mapsShortExact_mirabolicRankCast` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.mapsShortExact_mirabolicRankCast` |
| `Langlands.Derivative.LevelCalculus.mapsShortExact_phiMinusIterate` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.mapsShortExact_phiMinusIterate` |
| `Langlands.Derivative.LevelCalculus.mapsShortExact_mirabolicDerivative` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.mapsShortExact_mirabolicDerivative` |
| `Langlands.Derivative.LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder` |
| `Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_level` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_level` |
| `Langlands.Derivative.LevelCalculus.level_le_of_imp` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_le_of_imp` |
| `Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_iff_of_iso` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_iff_of_iso` |
| `Langlands.Derivative.LevelCalculus.level_eq_of_iso` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_eq_of_iso` |
| `Langlands.Derivative.LevelCalculus.level_mirabolicRankCast` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_mirabolicRankCast` |
| `Langlands.Derivative.LevelCalculus.nontrivial_of_hasNonzeroDerivative` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.nontrivial_of_hasNonzeroDerivative` |
| `Langlands.Derivative.LevelCalculus.level_pos` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_pos` |
| `Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_of_injective` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_of_injective` |
| `Langlands.Derivative.LevelCalculus.level_le_of_injective` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_le_of_injective` |
| `Langlands.Derivative.LevelCalculus.level_le_max_of_isShortExact` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_le_max_of_isShortExact` |
| `Langlands.Derivative.LevelCalculus.nontrivial_mirabolicDerivative_cast_congr` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.nontrivial_mirabolicDerivative_cast_congr` |
| `Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast` |
| `Langlands.Derivative.LevelCalculus.mirabolicDerivative_succ_cast_obj` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.mirabolicDerivative_succ_cast_obj` |
| `Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff` |
| `Langlands.Derivative.LevelCalculus.level_le_level_phiMinus_succ` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_le_level_phiMinus_succ` |
| `Langlands.Derivative.LevelCalculus.level_eq_level_phiMinus_succ` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_eq_level_phiMinus_succ` |
| `Langlands.Derivative.LevelCalculus.level_le_one_of_subsingleton_phiMinus` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_le_one_of_subsingleton_phiMinus` |
| `Langlands.Derivative.LevelCalculus.nontrivial_phiMinus_iff` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.nontrivial_phiMinus_iff` |
| `Langlands.Derivative.LevelCalculus.level_eq_of_isHomogeneous` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.level_eq_of_isHomogeneous` |
| `Langlands.Derivative.LevelCalculus.isHomogeneous_of_forall_injective` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.isHomogeneous_of_forall_injective` |
| `Langlands.Derivative.LevelCalculus.isHomogeneous_of_iso` | `Langlands.AllFieldBZ.Derivative.LevelCalculus.isHomogeneous_of_iso` |

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
