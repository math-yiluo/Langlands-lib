# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSlices`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSlices` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSlices`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSlices` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Determinant-slice expansion of the actual unequal-rank integrals**

For a p-adic field, every quotient measure and every rectangular measure, absolute
convergence of the actual unequal-rank JPSS integral at `s` makes its slice coefficients
at zero absolutely summable against `(q^(-s))^m`, with sum the integral at `s`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticBridge`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankSliceExpansionProof`
- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.unequalRankSliceCoefficient` (def): The slice coefficient of the unequal-rank integral: the restricted integral over the
  determinant slice `m` of the inner rectangular integral at `s = 0`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.unequalRankIntegrand_eq_mul_spectralPoint_zpow` (theorem): On the determinant slice `m`, the unequal-rank integrand at `s` is its value at zero
  times `(q^(-s))^m`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.unequalRank_sliceExpansion` (theorem): At a parameter of absolute convergence, the actual unequal-rank integral is the
  absolutely summable series of its slice coefficients against `(q^(-s))^m`.
