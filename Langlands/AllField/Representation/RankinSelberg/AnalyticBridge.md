# All-field port of `Langlands.Representation.RankinSelberg.AnalyticBridge`

`Langlands.AllField.Representation.RankinSelberg.AnalyticBridge` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AnalyticBridge`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.AnalyticBridge` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The JPSS analytic statements and the intrinsic zeta-value sets**

For a representation of Whittaker type with a specified nonzero functional, the
intrinsic zeta-value sets of `LocalFactor` coincide with the per-functional rational
values of `AnalyticStatement` once every model integral converges on a right half-plane.
Consequently each analytic conclusion, and each p-adic analytic statement, supplies the
existence proof required by the conditional L-factors. Nothing analytic is proved here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankAnalyticStatement.normalizedGeneratorExists` (theorem): The p-adic equal-rank analytic statement supplies, for every pair of Whittaker
  type, the existence proof required by `equalRankLFactor`, with the residue cardinality,
  the normalized absolute value and any compatible quotient measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.exists_eq_smul_of_linearEquiv`, `Langlands.RankinSelberg.IsOfWhittakerType.exists_ne_zero`, `Langlands.RankinSelberg.IsOfWhittakerType.eq_smul`, `Langlands.RankinSelberg.equalRankValuesOf_coefficientModel_subset`, `Langlands.RankinSelberg.equalRankValuesOf_coefficientModel_eq`, `Langlands.RankinSelberg.equalRankZetaValues_eq_rationalValues`, `Langlands.RankinSelberg.EqualRankAnalyticConclusion.zetaValues_eq`, `Langlands.RankinSelberg.EqualRankAnalyticConclusion.hasCommonDenominator`, `Langlands.RankinSelberg.EqualRankAnalyticConclusion.normalizedGeneratorExists`, `Langlands.RankinSelberg.EqualRankAnalyticConclusion.isEqualRankLPolynomial_iff`, `Langlands.RankinSelberg.unequalRankValuesOf_coefficientModel_subset`, `Langlands.RankinSelberg.unequalRankValuesOf_coefficientModel_eq`, `Langlands.RankinSelberg.unequalRankZetaValues_eq_rationalValues`, `Langlands.RankinSelberg.UnequalRankAnalyticConclusion.zetaValues_eq`, `Langlands.RankinSelberg.UnequalRankAnalyticConclusion.hasCommonDenominator`, `Langlands.RankinSelberg.UnequalRankAnalyticConclusion.normalizedGeneratorExists`, `Langlands.RankinSelberg.UnequalRankAnalyticConclusion.isUnequalRankLPolynomial_iff`, `Langlands.RankinSelberg.UnequalRankAnalyticStatement.normalizedGeneratorExists`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
