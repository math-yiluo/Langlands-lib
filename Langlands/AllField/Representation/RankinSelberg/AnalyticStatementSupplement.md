# All-field supplement to `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

`Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement` supplements the Library module `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`, the existing all-field port of `Langlands.Representation.RankinSelberg.AnalyticStatement`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.AnalyticStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPSS convergence and rationality on actual coefficient models**

These are proposition definitions, not proofs of the JPSS analytic theorem.
The quotient measure is any measure satisfying the published compatibility
predicate `QuotientIntegration.IsCompatible`; its existence is a separate
proposition. The scope is admissible finite-type Whittaker type, including
reducible representations.

## Imports from the port

- `Langlands.AllField.Group.GL.PadicSupplement`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.QuotientHaarExistenceStatement` (def): Existence of a quotient measure on each actual left-unipotent quotient
  `N_(n+1) \ GL_(n+1)`, compatible with the normalized Haar measures of
  `RankinSelberg.Measures`. Right invariance of the unipotent Haar measure,
  which the published compatibility predicate presupposes, is part of the claim.
  No representation or zeta integral occurs.
- `Langlands.AllField.RankinSelberg.EqualRankAnalyticStatement` (def): JPSS Theorem 2.7(i)-(ii), equal rank, over every specified p-adic field.
  Every character, representation, nonzero functional and compatible quotient
  measure is quantified explicitly.

Declarations of the original re-declared by `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement` and therefore not here: `Langlands.RankinSelberg.normalizedAbsoluteValue`, `Langlands.RankinSelberg.normalizedAbsoluteValue_apply`, `Langlands.RankinSelberg.UnequalRankAnalyticStatement`, `Langlands.RankinSelberg.UnequalRankCommonGeneratorStatement`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.spectralPoint_eq_spectralParameter`, `Langlands.RankinSelberg.IsOfWhittakerType`, `Langlands.RankinSelberg.equalRankRationalValues`, `Langlands.RankinSelberg.EqualRankAnalyticConclusion`, `Langlands.RankinSelberg.unequalRankRationalValues`, `Langlands.RankinSelberg.UnequalRankAnalyticConclusion`, `Langlands.RankinSelberg.unequalRankValuesAt`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
