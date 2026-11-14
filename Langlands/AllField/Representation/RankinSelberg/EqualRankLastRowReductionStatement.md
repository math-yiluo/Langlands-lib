# All-field port of `Langlands.Representation.RankinSelberg.EqualRankLastRowReductionStatement`

`Langlands.AllField.Representation.RankinSelberg.EqualRankLastRowReductionStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankLastRowReductionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankLastRowReductionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Equal-rank integrals with a last-row orbit cutoff**

JPSS (1983), printed 449, displays (1) and (3): an equal-rank integral whose
Schwartz variable is the indicator of the last-row orbit of a small compact
open subgroup reduces to the corank-one integral of the restrictions to
`diag(h, 1)`. This module only defines the proposition.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankLastRowReductionStatement` (def): For compatible quotient measures in ranks `n + 2` and `n + 1` and a compact
  open subgroup `J` of `GL_(n+2)`, there is one positive constant `c` such that,
  for all right `J`-invariant `W, W'`, the restriction `W''` of `W'` to
  `diag(h, 1)`, and the exact indicator `Φ` of the last-row orbit of `J`, the
  equal-rank integral converges exactly when the corank-one integral at `s - 1/2`
  does, and then equals `c` times it.
