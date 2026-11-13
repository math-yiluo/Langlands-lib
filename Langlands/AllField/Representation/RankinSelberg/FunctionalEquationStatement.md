# All-field port of `Langlands.Representation.RankinSelberg.FunctionalEquationStatement`

`Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.FunctionalEquationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.FunctionalEquationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual dual test data and proposition definitions for JPSS Theorem 2.7(iii).

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankFunctionalEquationStatement` (def): JPSS Theorem 2.7(iii), every pair of positive unequal ranks. The same
  epsilon monomial works for every `j`, with complementary dual block `k`.
  The rectangle measures come from the same self-dual scalar measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.standardCharacter_scale`, `Langlands.RankinSelberg.standardCharacter_scale_neg_one`, `Langlands.RankinSelberg.inverseStandardCharacter_scale_neg_one`, `Langlands.RankinSelberg.firstDualFunction`, `Langlands.RankinSelberg.secondDualFunction`, `Langlands.RankinSelberg.firstDualFunction_apply`, `Langlands.RankinSelberg.secondDualFunction_apply`, `Langlands.RankinSelberg.translateWhittaker`, `Langlands.RankinSelberg.translateWhittaker_apply`, `Langlands.RankinSelberg.blockWeylAt`, `Langlands.RankinSelberg.HasModelMinusOneScalar`, `Langlands.RankinSelberg.HasModelMinusOneScalar.unique`, `Langlands.RankinSelberg.epsilonMonomial`, `Langlands.RankinSelberg.epsilonMonomial_ne_zero`, `Langlands.RankinSelberg.NormalizedFunctionalEquation`, `Langlands.RankinSelberg.dualEqualRankModelIntegral`, `Langlands.RankinSelberg.dualEqualRankRationalValues`, `Langlands.RankinSelberg.EqualRankFunctionalEquationConclusion`, `Langlands.RankinSelberg.unequalRankIntegralAt`, `Langlands.RankinSelberg.dualUnequalRankModelIntegralAt`, `Langlands.RankinSelberg.dualUnequalRankRationalValuesAt`, `Langlands.RankinSelberg.UnequalRankFunctionalEquationConclusion`, `Langlands.RankinSelberg.EqualRankFunctionalEquationStatement`, `Langlands.RankinSelberg.Theorem27Statement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
