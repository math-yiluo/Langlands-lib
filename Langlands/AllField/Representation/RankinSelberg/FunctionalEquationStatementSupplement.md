# All-field supplement to `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement`

`Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement` supplements the Library module `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement`, the existing all-field port of `Langlands.Representation.RankinSelberg.FunctionalEquationStatement`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.FunctionalEquationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual dual test data and proposition definitions for JPSS Theorem 2.7(iii).

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankFunctionalEquationStatement` (def): JPSS Theorem 2.7(iii), equal positive ranks, with the actual plus-sign
  Fourier transform and the supplied scalar self-dual Haar measure.

Declarations of the original re-declared by `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement` and therefore not here: `Langlands.RankinSelberg.UnequalRankFunctionalEquationStatement`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.standardCharacter_scale`, `Langlands.RankinSelberg.standardCharacter_scale_neg_one`, `Langlands.RankinSelberg.inverseStandardCharacter_scale_neg_one`, `Langlands.RankinSelberg.firstDualFunction`, `Langlands.RankinSelberg.secondDualFunction`, `Langlands.RankinSelberg.firstDualFunction_apply`, `Langlands.RankinSelberg.secondDualFunction_apply`, `Langlands.RankinSelberg.translateWhittaker`, `Langlands.RankinSelberg.translateWhittaker_apply`, `Langlands.RankinSelberg.blockWeylAt`, `Langlands.RankinSelberg.HasModelMinusOneScalar`, `Langlands.RankinSelberg.HasModelMinusOneScalar.unique`, `Langlands.RankinSelberg.epsilonMonomial`, `Langlands.RankinSelberg.epsilonMonomial_ne_zero`, `Langlands.RankinSelberg.NormalizedFunctionalEquation`, `Langlands.RankinSelberg.dualEqualRankModelIntegral`, `Langlands.RankinSelberg.dualEqualRankRationalValues`, `Langlands.RankinSelberg.EqualRankFunctionalEquationConclusion`, `Langlands.RankinSelberg.unequalRankIntegralAt`, `Langlands.RankinSelberg.dualUnequalRankModelIntegralAt`, `Langlands.RankinSelberg.dualUnequalRankRationalValuesAt`, `Langlands.RankinSelberg.UnequalRankFunctionalEquationConclusion`, `Langlands.RankinSelberg.Theorem27Statement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
